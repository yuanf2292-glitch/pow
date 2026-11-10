// amnt_solve.c — CPU solver for AgentMining AMNT (BSC).
//
// Proof (verified against live contract 0x2d07B9CcDF5FCdbE26167358B94eeb4c9E995e4E):
//   keccak256(abi.encode(sessionSeedBase, wallet, agentId, lane, day, nonce)) <= target
// Preimage = 192 bytes, 6 x 32-byte words, big-endian, left-padded:
//   word0 = seed (bytes32)
//   word1 = wallet address (20 bytes, left-padded to 32)
//   word2 = agentId (uint256)
//   word3 = lane (uint8 value 2, left-padded to 32)
//   word4 = day (uint256, 0 for day 0)
//   word5 = nonce (uint256)
// CPU lane = 2, CPU target = 2^228 - 1 (28 leading zero bits).
// Expected work per proof ~2^28 = ~268M hashes.
//
// Speed trick: keccak256 rate is 136 bytes, so the 192-byte preimage absorbs
// in 2 blocks. Block 1 (bytes 0..135 = words 0..3 + first 8 bytes of day) is
// FIXED for a given seed/wallet/agentId/lane/day, so its permutation is done
// ONCE. Per nonce only block 2 (56 bytes + padding) needs one permutation.
// Nonce lives in block-2 lane 6 (bytes 184..191 BE) => st[6] ^= bswap64(nonce).
// Pad: st[7] ^= 0x01, st[16] ^= 0x80<<56.
//
// Usage:
//   ./amnt_solve --seed <hex32> --wallet <0xaddr> --agentid <decimal>
//                 --lane 2 --day 0 --start-nonce <n> --count <k> --threads <n>
//                 [--zerobits 28]
// Prints FOUND lines: nonce (decimal) + digest hex, plus hash rate.
// No network, no signing, no on-chain submission — offline solving only.
//
// Portable: plain C99 + pthreads, no extra deps.
//   gcc -O3 -o amnt_solve amnt_solve.c -lpthread
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

// ---- keccak-f1600 (from ~/workspace/tools/keccak_pow.c) ----
static const uint64_t RC[24] = {0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,0x8000000080008000ULL,0x000000000000808bULL,0x0000000080000001ULL,0x8000000080008081ULL,0x8000000000008009ULL,0x000000000000008aULL,0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,0x8000000000008002ULL,0x8000000000000080ULL,0x000000000000800aULL,0x800000008000000aULL,0x8000000080008081ULL,0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL};
static const int R[24] = {1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44};
static const int P[24] = {10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1};
static inline uint64_t rol(uint64_t x,int n){return (x<<n)|(x>>(64-n));}
static void keccakf(uint64_t st[25]){
 for(int r=0;r<24;r++){
  uint64_t bc[5];
  for(int i=0;i<5;i++) bc[i]=st[i]^st[i+5]^st[i+10]^st[i+15]^st[i+20];
  for(int i=0;i<5;i++){uint64_t t=bc[(i+4)%5]^rol(bc[(i+1)%5],1);for(int j=0;j<25;j+=5)st[j+i]^=t;}
  uint64_t t=st[1];
  for(int i=0;i<24;i++){int j=P[i];uint64_t tmp=st[j];st[j]=rol(t,R[i]);t=tmp;}
  for(int j=0;j<25;j+=5){for(int i=0;i<5;i++)bc[i]=st[j+i];for(int i=0;i<5;i++)st[j+i]^=(~bc[(i+1)%5])&bc[(i+2)%5];}
  st[0]^=RC[r];
 }
}
// Full keccak256 (used only by selftest).
static void keccak256_full(const uint8_t *in,size_t inlen,uint8_t *out){
 uint64_t st[25]={0};uint8_t temp[144];size_t rsiz=136;size_t rsizw=rsiz/8;
 while(inlen>=rsiz){for(size_t i=0;i<rsizw;i++){uint64_t w;memcpy(&w,in+i*8,8);st[i]^=w;}keccakf(st);in+=rsiz;inlen-=rsiz;}
 memset(temp,0,sizeof(temp));memcpy(temp,in,inlen);temp[inlen]=0x01;temp[rsiz-1]|=0x80;
 for(size_t i=0;i<rsizw;i++){uint64_t w;memcpy(&w,temp+i*8,8);st[i]^=w;}
 keccakf(st);memcpy(out,st,32);
}

// ---- hex / decimal parsing ----
static int hexval(char c){if(c>='0'&&c<='9')return c-'0';if(c>='a'&&c<='f')return c-'a'+10;if(c>='A'&&c<='F')return c-'A'+10;return -1;}
static int parse_hex(const char *hex,uint8_t *out,size_t n){
 if(hex[0]=='0'&&(hex[1]=='x'||hex[1]=='X'))hex+=2;
 if(strlen(hex)!=n*2)return -1;
 for(size_t i=0;i<n;i++){int hi=hexval(hex[2*i]),lo=hexval(hex[2*i+1]);if(hi<0||lo<0)return -1;out[i]=(uint8_t)((hi<<4)|lo);}
 return 0;
}
// decimal string -> 32-byte big-endian
static int parse_dec256(const char *dec,uint8_t *out){
 memset(out,0,32);
 for(const char *p=dec;*p;p++){
  if(*p<'0'||*p>'9')return -1;
  int carry=*p-'0';
  for(int i=31;i>=0;i--){int v=out[i]*10+carry;out[i]=(uint8_t)(v&0xff);carry=v>>8;}
  if(carry)return -1; // > 2^256
 }
 return 0;
}

// ---- globals ----
static uint64_t BASE[25];          // keccak state after absorbing block 1
static int ZEROBITS = 28;
static uint64_t START_NONCE = 0;
static int NTHREADS = 4;
static int WANT_COUNT = 1;
static atomic_int found_count = 0;
static atomic_int stop_flag = 0;
static atomic_ullong total_tried = 0;
static struct timespec T0;
static pthread_mutex_t print_mu = PTHREAD_MUTEX_INITIALIZER;

static double elapsed_s(void){
 struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);
 return (t.tv_sec-T0.tv_sec)+(t.tv_nsec-T0.tv_nsec)/1e9;
}

static int digest_ok(const uint8_t *h){
 int full=ZEROBITS/8, rem=ZEROBITS%8;
 for(int i=0;i<full;i++) if(h[i]!=0) return 0;
 if(rem && (h[full]>>(8-rem))!=0) return 0;
 return 1;
}

static void *worker(void *arg){
 long tid=(long)arg;
 uint64_t st[25];
 uint64_t nonce=START_NONCE+(uint64_t)tid;
 uint64_t local=0;
 while(!atomic_load(&stop_flag)){
  memcpy(st,BASE,sizeof(st));
  st[6]  ^= __builtin_bswap64(nonce);  // block2 lane 6 = nonce word bytes 184..191 BE
  st[7]  ^= 0x01ULL;                    // block2 byte 56 = keccak pad 0x01
  st[16] ^= 0x8000000000000000ULL;      // block2 byte 135 |= 0x80
  keccakf(st);
  uint8_t h[32];memcpy(h,st,32);
  local++;
  if((local & 0xFFFF)==0){ // report every ~64K hashes per thread
   atomic_fetch_add(&total_tried,0x10000ULL);
  }
  if(digest_ok(h)){
   int c=atomic_fetch_add(&found_count,1)+1;
   pthread_mutex_lock(&print_mu);
   printf("FOUND nonce=%llu hash=", (unsigned long long)nonce);
   for(int i=0;i<32;i++)printf("%02x",h[i]);
   printf(" elapsed=%.1fs tried=%llu rate=%.0f H/s\n",
     elapsed_s(), (unsigned long long)atomic_load(&total_tried),
     (double)atomic_load(&total_tried)/elapsed_s());
   fflush(stdout);
   pthread_mutex_unlock(&print_mu);
   if(c>=WANT_COUNT) atomic_store(&stop_flag,1);
  }
  nonce+=(uint64_t)NTHREADS;
  // avoid nonce wrap / overflow guard
  if(nonce<START_NONCE) break;
 }
 // flush remainder of local counter
 uint64_t rem=local & 0xFFFF;
 if(rem) atomic_fetch_add(&total_tried,rem);
 return NULL;
}

static void usage(const char *p){
 fprintf(stderr,
  "usage: %s --seed <hex32> --wallet <0xaddr> --agentid <decimal>\n"
  "          [--lane 2] [--day 0] [--start-nonce N] [--count K] [--threads N]\n"
  "          [--zerobits 28] [--selftest]\n",p);
}

int main(int argc,char **argv){
 const char *seed_hex=NULL,*wallet_hex=NULL,*agentid_dec=NULL;
 uint64_t lane=2, day=0;
 int selftest=0;
 for(int i=1;i<argc;i++){
  if(!strcmp(argv[i],"--seed")&&i+1<argc) seed_hex=argv[++i];
  else if(!strcmp(argv[i],"--wallet")&&i+1<argc) wallet_hex=argv[++i];
  else if(!strcmp(argv[i],"--agentid")&&i+1<argc) agentid_dec=argv[++i];
  else if(!strcmp(argv[i],"--lane")&&i+1<argc) lane=strtoull(argv[++i],NULL,10);
  else if(!strcmp(argv[i],"--day")&&i+1<argc) day=strtoull(argv[++i],NULL,10);
  else if(!strcmp(argv[i],"--start-nonce")&&i+1<argc) START_NONCE=strtoull(argv[++i],NULL,10);
  else if(!strcmp(argv[i],"--count")&&i+1<argc) WANT_COUNT=atoi(argv[++i]);
  else if(!strcmp(argv[i],"--threads")&&i+1<argc) NTHREADS=atoi(argv[++i]);
  else if(!strcmp(argv[i],"--zerobits")&&i+1<argc) ZEROBITS=atoi(argv[++i]);
  else if(!strcmp(argv[i],"--selftest")) selftest=1;
  else {usage(argv[0]);return 1;}
 }
 if(selftest){
  uint8_t h[32];char hex[65];
  keccak256_full((const uint8_t*)"",0,h);
  for(int i=0;i<32;i++)sprintf(hex+2*i,"%02x",h[i]);
  printf("selftest-empty %s (%s)\n",
   strcmp(hex,"c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")==0?"PASS":"FAIL",hex);
  keccak256_full((const uint8_t*)"abc",3,h);
  for(int i=0;i<32;i++)sprintf(hex+2*i,"%02x",h[i]);
  printf("selftest-abc %s (%s)\n",
   strcmp(hex,"4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")==0?"PASS":"FAIL",hex);
  return 0;
 }
 if(!seed_hex||!wallet_hex||!agentid_dec){usage(argv[0]);return 1;}
 if(NTHREADS<1)NTHREADS=1;
 if(WANT_COUNT<1)WANT_COUNT=1;

 // Build the 192-byte preimage template (nonce word left zero).
 uint8_t pre[192];memset(pre,0,sizeof(pre));
 uint8_t seed[32], wallet[20], agentid[32];
 if(parse_hex(seed_hex,seed,32)!=0){fprintf(stderr,"bad --seed (need 64 hex chars)\n");return 1;}
 if(parse_hex(wallet_hex,wallet,20)!=0){fprintf(stderr,"bad --wallet (need 40 hex chars)\n");return 1;}
 if(parse_dec256(agentid_dec,agentid)!=0){fprintf(stderr,"bad --agentid (decimal, <= 2^256-1)\n");return 1;}
 memcpy(pre+0,  seed,32);            // word0 seed
 memcpy(pre+32+12, wallet,20);       // word1 wallet left-padded
 memcpy(pre+64, agentid,32);         // word2 agentId
 pre[96+31]=(uint8_t)lane;           // word3 lane
 for(int i=0;i<8;i++) pre[128+24+i]=(uint8_t)(day>>(56-8*i)); // word4 day BE
 // word5 (nonce) stays 0 in the template; filled per-iteration via lane 23.

 // Absorb block 1 (bytes 0..135) once -> BASE state.
 uint64_t st[25]={0};
 for(int i=0;i<17;i++){uint64_t w;memcpy(&w,pre+i*8,8);st[i]^=w;}
 keccakf(st);
 memcpy(BASE,st,sizeof(BASE));

 clock_gettime(CLOCK_MONOTONIC,&T0);
 printf("AMNT solver: lane=%llu day=%llu zerobits=%d target=2^%d-1 threads=%d start=%llu count=%d\n",
   (unsigned long long)lane,(unsigned long long)day,ZEROBITS,256-ZEROBITS,NTHREADS,
   (unsigned long long)START_NONCE,WANT_COUNT);
 fflush(stdout);

 pthread_t *th=malloc(sizeof(pthread_t)*NTHREADS);
 for(long i=0;i<NTHREADS;i++) pthread_create(&th[i],NULL,worker,(void*)i);
 // progress reporter (main thread)
 double last_print=0;
 while(!atomic_load(&stop_flag)){
  struct timespec ts={0,200000000};nanosleep(&ts,NULL); // 0.2s poll so exit is prompt
  if(atomic_load(&stop_flag))break;
  double el=elapsed_s();
  if(el-last_print<5.0)continue; // one progress line per 5s
  last_print=el;
  unsigned long long tr=atomic_load(&total_tried);
  printf("PROGRESS tried=%llu elapsed=%.0fs rate=%.0f H/s found=%d\n",
    tr,el,(double)tr/el,atomic_load(&found_count));
  fflush(stdout);
 }
 for(int i=0;i<NTHREADS;i++) pthread_join(th[i],NULL);
 double el=elapsed_s();
 unsigned long long tr=atomic_load(&total_tried);
 int fc=atomic_load(&found_count);
 printf("DONE found=%d tried=%llu elapsed=%.1fs avg_rate=%.0f H/s (%.2f MH/s)\n",
   fc,tr,el,(double)tr/el,(double)tr/el/1e6);
 if(fc>=WANT_COUNT) printf("PER-PROOF avg time: %.1fs\n", el/fc);
 return fc>=WANT_COUNT?0:2;
}
