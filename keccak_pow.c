#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static const uint64_t RC[24] = {0x0000000000000001ULL,0x0000000000008082ULL,0x800000000000808aULL,0x8000000080008000ULL,0x000000000000808bULL,0x0000000080000001ULL,0x8000000080008081ULL,0x8000000000008009ULL,0x000000000000008aULL,0x0000000000000088ULL,0x0000000080008009ULL,0x000000008000000aULL,0x000000008000808bULL,0x800000000000008bULL,0x8000000000008089ULL,0x8000000000008003ULL,0x8000000000008002ULL,0x8000000000000080ULL,0x000000000000800aULL,0x800000008000000aULL,0x8000000080008081ULL,0x8000000000008080ULL,0x0000000080000001ULL,0x8000000080008008ULL};
static const int R[24] = {1,3,6,10,15,21,28,36,45,55,2,14,27,41,56,8,25,43,62,18,39,61,20,44};
static const int P[24] = {10,7,11,17,18,3,5,16,8,21,24,4,15,23,19,13,12,2,20,14,22,9,6,1};
static uint64_t rol(uint64_t x,int n){return (x<<n)|(x>>(64-n));}
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
static void keccak256(const uint8_t *in,size_t inlen,uint8_t *out){
 uint64_t st[25]={0};uint8_t temp[144];size_t rsiz=136;size_t rsizw=rsiz/8;
 while(inlen>=rsiz){for(size_t i=0;i<rsizw;i++){uint64_t w;memcpy(&w,in+i*8,8);st[i]^=w;}keccakf(st);in+=rsiz;inlen-=rsiz;}
 memset(temp,0,sizeof(temp));memcpy(temp,in,inlen);temp[inlen]=0x01;temp[rsiz-1]|=0x80;
 for(size_t i=0;i<rsizw;i++){uint64_t w;memcpy(&w,temp+i*8,8);st[i]^=w;}
 keccakf(st);memcpy(out,st,32);
}
static int hexval(char c){if(c>='0'&&c<='9')return c-'0';if(c>='a'&&c<='f')return c-'a'+10;if(c>='A'&&c<='F')return c-'A'+10;return -1;}
static int parse_hex(const char *hex,uint8_t *out,size_t n){for(size_t i=0;i<n;i++){int hi=hexval(hex[2*i]),lo=hexval(hex[2*i+1]);if(hi<0||lo<0)return -1;out[i]=(hi<<4)|lo;}return 0;}
int main(int argc,char **argv){
 if(argc>=2&&strcmp(argv[1],"test")==0){uint8_t h[32];keccak256((const uint8_t*)"",0,h);printf("empty=");for(int i=0;i<32;i++)printf("%02x",h[i]);printf("\n");keccak256((const uint8_t*)"abc",3,h);printf("abc=");for(int i=0;i<32;i++)printf("%02x",h[i]);printf("\n");return 0;}
 if(argc<4){fprintf(stderr,"usage: %s <sender_hex40> <freeMintedBy_dec> <zerobits> [start_nonce] [max_iter]\n",argv[0]);return 1;}
 uint8_t sender[20];if(parse_hex(argv[1],sender,20)!=0){fprintf(stderr,"bad sender hex\n");return 1;}
 unsigned long long fmb=strtoull(argv[2],NULL,10);
 int zerobits=atoi(argv[3]);
 unsigned long long start=argc>4?strtoull(argv[4],NULL,10):0;
 unsigned long long maxiter=argc>5?strtoull(argv[5],NULL,10):0;
 uint8_t msg[84];memcpy(msg,sender,20);memset(msg+20,0,32);
 for(int i=0;i<8;i++)msg[20+24+i]=(fmb>>(56-8*i))&0xff;
 uint8_t hash[32];unsigned long long nonce=start;
 struct timespec t0,t1;clock_gettime(CLOCK_MONOTONIC,&t0);
 while(1){
  memset(msg+52,0,32);
  for(int i=0;i<8;i++)msg[52+24+i]=(nonce>>(56-8*i))&0xff;
  keccak256(msg,84,hash);
  int ok=1;int full=zerobits/8;int rem=zerobits%8;
  for(int i=0;i<full;i++)if(hash[i]!=0){ok=0;break;}
  if(ok&&rem){if((hash[full]>>(8-rem))!=0)ok=0;}
  if(ok){clock_gettime(CLOCK_MONOTONIC,&t1);double el=(t1.tv_sec-t0.tv_sec)+(t1.tv_nsec-t0.tv_nsec)/1e9;printf("FOUND nonce=%llu hash=",nonce);for(int i=0;i<32;i++)printf("%02x",hash[i]);printf(" elapsed=%.2fs rate=%.0f/s\n",el,(double)(nonce-start+1)/el);return 0;}
  nonce++;
  if(maxiter&&(nonce-start)>=maxiter){clock_gettime(CLOCK_MONOTONIC,&t1);double el=(t1.tv_sec-t0.tv_sec)+(t1.tv_nsec-t0.tv_nsec)/1e9;printf("NOTFOUND tried=%llu elapsed=%.2fs rate=%.0f/s\n",nonce-start,el,(double)(nonce-start)/el);return 2;}
 }
}
