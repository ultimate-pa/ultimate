// Simple, thoroughly commented implementation of DES / Triple DES in C
// Chris Hulbert - chris.hulbert@gmail.com - http://splinter.com.au/blog
// See http://orlingrabbe.com/des.htm for a great des description
// To compile this with Visual C, simply do: cl c_des.c

#include <stdio.h>
#include <string.h>

typedef unsigned char byte;
 
// Does the DES PC1 permutation, taking a 64 bit key and converting it to 56 bits
// To test the PC1 permutation:
// Example: From the original 64-bit key
// K = 00010011 00110100 01010111 01111001 10011011 10111100 11011111 11110001
//   = 0x13,0x34,0x57,0x79,0x9B,0xBC,0xDF,0xF1
// we get the 56-bit permutation
// K+ = 1111000 0110011 0010101 0101111 0101010 1011001 1001111 0001111
//    = 11110000 11001100 10101010 11110101 01010110 01100111 10001111
//    = f0       cc       aa       f5       56       67       8f
// And it does in fact work!
void PC1(const byte *k, byte *k56)
{
  k56[0] =  (((k[7]>>7)&1)<<7) +  (((k[6]>>7)&1)<<6) +  (((k[5]>>7)&1)<<5) +  (((k[4]>>7)&1)<<4) +  (((k[3]>>7)&1)<<3) +  (((k[2]>>7)&1)<<2) +  (((k[1]>>7)&1)<<1) +  (((k[0]>>7)&1)<<0);
  k56[1] =  (((k[7]>>6)&1)<<7) +  (((k[6]>>6)&1)<<6) +  (((k[5]>>6)&1)<<5) +  (((k[4]>>6)&1)<<4) +  (((k[3]>>6)&1)<<3) +  (((k[2]>>6)&1)<<2) +  (((k[1]>>6)&1)<<1) +  (((k[0]>>6)&1)<<0);
  k56[2] =  (((k[7]>>5)&1)<<7) +  (((k[6]>>5)&1)<<6) +  (((k[5]>>5)&1)<<5) +  (((k[4]>>5)&1)<<4) +  (((k[3]>>5)&1)<<3) +  (((k[2]>>5)&1)<<2) +  (((k[1]>>5)&1)<<1) +  (((k[0]>>5)&1)<<0);
  k56[3] =  (((k[7]>>4)&1)<<7) +  (((k[6]>>4)&1)<<6) +  (((k[5]>>4)&1)<<5) +  (((k[4]>>4)&1)<<4) +  (((k[7]>>1)&1)<<3) +  (((k[6]>>1)&1)<<2) +  (((k[5]>>1)&1)<<1) +  (((k[4]>>1)&1)<<0);
  k56[4] =  (((k[3]>>1)&1)<<7) +  (((k[2]>>1)&1)<<6) +  (((k[1]>>1)&1)<<5) +  (((k[0]>>1)&1)<<4) +  (((k[7]>>2)&1)<<3) +  (((k[6]>>2)&1)<<2) +  (((k[5]>>2)&1)<<1) +  (((k[4]>>2)&1)<<0);
  k56[5] =  (((k[3]>>2)&1)<<7) +  (((k[2]>>2)&1)<<6) +  (((k[1]>>2)&1)<<5) +  (((k[0]>>2)&1)<<4) +  (((k[7]>>3)&1)<<3) +  (((k[6]>>3)&1)<<2) +  (((k[5]>>3)&1)<<1) +  (((k[4]>>3)&1)<<0);
  k56[6] =  (((k[3]>>3)&1)<<7) +  (((k[2]>>3)&1)<<6) +  (((k[1]>>3)&1)<<5) +  (((k[0]>>3)&1)<<4) +  (((k[3]>>4)&1)<<3) +  (((k[2]>>4)&1)<<2) +  (((k[1]>>4)&1)<<1) +  (((k[0]>>4)&1)<<0);
}

// Does the DES PC2 permutation, taking a 56bit CnDn and returning a 48bit Kn 
void PC2(const byte *in, byte *out)
{
  out[0] =  (((in[1]>>2)&1)<<7) +   (((in[2]>>7)&1)<<6) +   (((in[1]>>5)&1)<<5) +   (((in[2]>>0)&1)<<4) +   (((in[0]>>7)&1)<<3) +   (((in[0]>>3)&1)<<2) +   (((in[0]>>5)&1)<<1) +   (((in[3]>>4)&1)<<0);
  out[1] =  (((in[1]>>1)&1)<<7) +   (((in[0]>>2)&1)<<6) +   (((in[2]>>3)&1)<<5) +   (((in[1]>>6)&1)<<4) +   (((in[2]>>1)&1)<<3) +   (((in[2]>>5)&1)<<2) +   (((in[1]>>4)&1)<<1) +   (((in[0]>>4)&1)<<0);
  out[2] =  (((in[3]>>6)&1)<<7) +   (((in[0]>>0)&1)<<6) +   (((in[1]>>0)&1)<<5) +   (((in[0]>>1)&1)<<4) +   (((in[3]>>5)&1)<<3) +   (((in[2]>>4)&1)<<2) +   (((in[1]>>3)&1)<<1) +   (((in[0]>>6)&1)<<0);
  out[3] =  (((in[5]>>7)&1)<<7) +   (((in[6]>>4)&1)<<6) +   (((in[3]>>1)&1)<<5) +   (((in[4]>>3)&1)<<4) +   (((in[5]>>1)&1)<<3) +   (((in[6]>>1)&1)<<2) +   (((in[3]>>2)&1)<<1) +   (((in[4]>>0)&1)<<0);
  out[4] =  (((in[6]>>5)&1)<<7) +   (((in[5]>>3)&1)<<6) +   (((in[4]>>7)&1)<<5) +   (((in[5]>>0)&1)<<4) +   (((in[5]>>4)&1)<<3) +   (((in[6]>>7)&1)<<2) +   (((in[4]>>1)&1)<<1) +   (((in[6]>>0)&1)<<0);
  out[5] =  (((in[4]>>6)&1)<<7) +   (((in[6]>>3)&1)<<6) +   (((in[5]>>2)&1)<<5) +   (((in[5]>>6)&1)<<4) +   (((in[6]>>6)&1)<<3) +   (((in[4]>>4)&1)<<2) +   (((in[3]>>3)&1)<<1) +   (((in[3]>>0)&1)<<0);
}

// Does the Initial Permutation on the 64 bits of the message data. Output is also 64 bits.
// EG: M = 0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101 1110 1111
//       = 0123456789ABCDEF      
//    IP = 1100 1100 0000 0000 1100 1100 1111 1111 1111 0000 1010 1010 1111 0000 1010 1010
//       = CC00CCFFF0AAF0AA
void IP(const byte *in, byte *out)
{
  out[0] =  (((in[7]>>6)&1)<<7) +   (((in[6]>>6)&1)<<6) +   (((in[5]>>6)&1)<<5) +   (((in[4]>>6)&1)<<4) +   (((in[3]>>6)&1)<<3) +   (((in[2]>>6)&1)<<2) +   (((in[1]>>6)&1)<<1) +   (((in[0]>>6)&1)<<0);
  out[1] =  (((in[7]>>4)&1)<<7) +   (((in[6]>>4)&1)<<6) +   (((in[5]>>4)&1)<<5) +   (((in[4]>>4)&1)<<4) +   (((in[3]>>4)&1)<<3) +   (((in[2]>>4)&1)<<2) +   (((in[1]>>4)&1)<<1) +   (((in[0]>>4)&1)<<0);
  out[2] =  (((in[7]>>2)&1)<<7) +   (((in[6]>>2)&1)<<6) +   (((in[5]>>2)&1)<<5) +   (((in[4]>>2)&1)<<4) +   (((in[3]>>2)&1)<<3) +   (((in[2]>>2)&1)<<2) +   (((in[1]>>2)&1)<<1) +   (((in[0]>>2)&1)<<0);
  out[3] =  (((in[7]>>0)&1)<<7) +   (((in[6]>>0)&1)<<6) +   (((in[5]>>0)&1)<<5) +   (((in[4]>>0)&1)<<4) +   (((in[3]>>0)&1)<<3) +   (((in[2]>>0)&1)<<2) +   (((in[1]>>0)&1)<<1) +   (((in[0]>>0)&1)<<0);
  out[4] =  (((in[7]>>7)&1)<<7) +   (((in[6]>>7)&1)<<6) +   (((in[5]>>7)&1)<<5) +   (((in[4]>>7)&1)<<4) +   (((in[3]>>7)&1)<<3) +   (((in[2]>>7)&1)<<2) +   (((in[1]>>7)&1)<<1) +   (((in[0]>>7)&1)<<0);
  out[5] =  (((in[7]>>5)&1)<<7) +   (((in[6]>>5)&1)<<6) +   (((in[5]>>5)&1)<<5) +   (((in[4]>>5)&1)<<4) +   (((in[3]>>5)&1)<<3) +   (((in[2]>>5)&1)<<2) +   (((in[1]>>5)&1)<<1) +   (((in[0]>>5)&1)<<0);
  out[6] =  (((in[7]>>3)&1)<<7) +   (((in[6]>>3)&1)<<6) +   (((in[5]>>3)&1)<<5) +   (((in[4]>>3)&1)<<4) +   (((in[3]>>3)&1)<<3) +   (((in[2]>>3)&1)<<2) +   (((in[1]>>3)&1)<<1) +   (((in[0]>>3)&1)<<0);
  out[7] =  (((in[7]>>1)&1)<<7) +   (((in[6]>>1)&1)<<6) +   (((in[5]>>1)&1)<<5) +   (((in[4]>>1)&1)<<4) +   (((in[3]>>1)&1)<<3) +   (((in[2]>>1)&1)<<2) +   (((in[1]>>1)&1)<<1) +   (((in[0]>>1)&1)<<0);
}

// Does the IP-1 after the encryption rounds
void IPreverse(const byte *in, byte *out)
{
  out[0] =  (((in[4]>>0)&1)<<7) +   (((in[0]>>0)&1)<<6) +   (((in[5]>>0)&1)<<5) +   (((in[1]>>0)&1)<<4) +   (((in[6]>>0)&1)<<3) +   (((in[2]>>0)&1)<<2) +   (((in[7]>>0)&1)<<1) +   (((in[3]>>0)&1)<<0);
  out[1] =  (((in[4]>>1)&1)<<7) +   (((in[0]>>1)&1)<<6) +   (((in[5]>>1)&1)<<5) +   (((in[1]>>1)&1)<<4) +   (((in[6]>>1)&1)<<3) +   (((in[2]>>1)&1)<<2) +   (((in[7]>>1)&1)<<1) +   (((in[3]>>1)&1)<<0);
  out[2] =  (((in[4]>>2)&1)<<7) +   (((in[0]>>2)&1)<<6) +   (((in[5]>>2)&1)<<5) +   (((in[1]>>2)&1)<<4) +   (((in[6]>>2)&1)<<3) +   (((in[2]>>2)&1)<<2) +   (((in[7]>>2)&1)<<1) +   (((in[3]>>2)&1)<<0);
  out[3] =  (((in[4]>>3)&1)<<7) +   (((in[0]>>3)&1)<<6) +   (((in[5]>>3)&1)<<5) +   (((in[1]>>3)&1)<<4) +   (((in[6]>>3)&1)<<3) +   (((in[2]>>3)&1)<<2) +   (((in[7]>>3)&1)<<1) +   (((in[3]>>3)&1)<<0);
  out[4] =  (((in[4]>>4)&1)<<7) +   (((in[0]>>4)&1)<<6) +   (((in[5]>>4)&1)<<5) +   (((in[1]>>4)&1)<<4) +   (((in[6]>>4)&1)<<3) +   (((in[2]>>4)&1)<<2) +   (((in[7]>>4)&1)<<1) +   (((in[3]>>4)&1)<<0);
  out[5] =  (((in[4]>>5)&1)<<7) +   (((in[0]>>5)&1)<<6) +   (((in[5]>>5)&1)<<5) +   (((in[1]>>5)&1)<<4) +   (((in[6]>>5)&1)<<3) +   (((in[2]>>5)&1)<<2) +   (((in[7]>>5)&1)<<1) +   (((in[3]>>5)&1)<<0);
  out[6] =  (((in[4]>>6)&1)<<7) +   (((in[0]>>6)&1)<<6) +   (((in[5]>>6)&1)<<5) +   (((in[1]>>6)&1)<<4) +   (((in[6]>>6)&1)<<3) +   (((in[2]>>6)&1)<<2) +   (((in[7]>>6)&1)<<1) +   (((in[3]>>6)&1)<<0);
  out[7] =  (((in[4]>>7)&1)<<7) +   (((in[0]>>7)&1)<<6) +   (((in[5]>>7)&1)<<5) +   (((in[1]>>7)&1)<<4) +   (((in[6]>>7)&1)<<3) +   (((in[2]>>7)&1)<<2) +   (((in[7]>>7)&1)<<1) +   (((in[3]>>7)&1)<<0);
}

// Does the 'E' permutation
// Takes 32 bits in and puts 48 bits out
// Eg: R0 = 1111 0000 1010 1010 1111 0000 1010 1010 
//  E(R0) = 011110 100001 010101 010101 011110 100001 010101 010101
// F0AAF0AA => 7A15557A1555
void E(const byte *in, byte *out)
{
  out[0] =  (((in[3]>>0)&1)<<7) +   (((in[0]>>7)&1)<<6) +   (((in[0]>>6)&1)<<5) +   (((in[0]>>5)&1)<<4) +   (((in[0]>>4)&1)<<3) +   (((in[0]>>3)&1)<<2) +   (((in[0]>>4)&1)<<1) +   (((in[0]>>3)&1)<<0);
  out[1] =  (((in[0]>>2)&1)<<7) +   (((in[0]>>1)&1)<<6) +   (((in[0]>>0)&1)<<5) +   (((in[1]>>7)&1)<<4) +   (((in[0]>>0)&1)<<3) +   (((in[1]>>7)&1)<<2) +   (((in[1]>>6)&1)<<1) +   (((in[1]>>5)&1)<<0);
  out[2] =  (((in[1]>>4)&1)<<7) +   (((in[1]>>3)&1)<<6) +   (((in[1]>>4)&1)<<5) +   (((in[1]>>3)&1)<<4) +   (((in[1]>>2)&1)<<3) +   (((in[1]>>1)&1)<<2) +   (((in[1]>>0)&1)<<1) +   (((in[2]>>7)&1)<<0);
  out[3] =  (((in[1]>>0)&1)<<7) +   (((in[2]>>7)&1)<<6) +   (((in[2]>>6)&1)<<5) +   (((in[2]>>5)&1)<<4) +   (((in[2]>>4)&1)<<3) +   (((in[2]>>3)&1)<<2) +   (((in[2]>>4)&1)<<1) +   (((in[2]>>3)&1)<<0);
  out[4] =  (((in[2]>>2)&1)<<7) +   (((in[2]>>1)&1)<<6) +   (((in[2]>>0)&1)<<5) +   (((in[3]>>7)&1)<<4) +   (((in[2]>>0)&1)<<3) +   (((in[3]>>7)&1)<<2) +   (((in[3]>>6)&1)<<1) +   (((in[3]>>5)&1)<<0);
  out[5] =  (((in[3]>>4)&1)<<7) +   (((in[3]>>3)&1)<<6) +   (((in[3]>>4)&1)<<5) +   (((in[3]>>3)&1)<<4) +   (((in[3]>>2)&1)<<3) +   (((in[3]>>1)&1)<<2) +   (((in[3]>>0)&1)<<1) +   (((in[0]>>7)&1)<<0);
}

// Does the 'P' permutation
// 32 bits in, 32 bits out
// Eg: 0101 1100 1000 0010 1011 0101 1001 0111  => 0010 0011 0100 1010 1010 1001 1011 1011
// 5C82B597 => 234AA9BB
void P(const byte *in, byte *out)
{
  out[0] =  (((in[1]>>0)&1)<<7) +   (((in[0]>>1)&1)<<6) +   (((in[2]>>4)&1)<<5) +   (((in[2]>>3)&1)<<4) +   (((in[3]>>3)&1)<<3) +   (((in[1]>>4)&1)<<2) +   (((in[3]>>4)&1)<<1) +   (((in[2]>>7)&1)<<0);
  out[1] =  (((in[0]>>7)&1)<<7) +   (((in[1]>>1)&1)<<6) +   (((in[2]>>1)&1)<<5) +   (((in[3]>>6)&1)<<4) +   (((in[0]>>3)&1)<<3) +   (((in[2]>>6)&1)<<2) +   (((in[3]>>1)&1)<<1) +   (((in[1]>>6)&1)<<0);
  out[2] =  (((in[0]>>6)&1)<<7) +   (((in[0]>>0)&1)<<6) +   (((in[2]>>0)&1)<<5) +   (((in[1]>>2)&1)<<4) +   (((in[3]>>0)&1)<<3) +   (((in[3]>>5)&1)<<2) +   (((in[0]>>5)&1)<<1) +   (((in[1]>>7)&1)<<0);
  out[3] =  (((in[2]>>5)&1)<<7) +   (((in[1]>>3)&1)<<6) +   (((in[3]>>2)&1)<<5) +   (((in[0]>>2)&1)<<4) +   (((in[2]>>2)&1)<<3) +   (((in[1]>>5)&1)<<2) +   (((in[0]>>4)&1)<<1) +   (((in[3]>>7)&1)<<0);
}

// S-box lookups transformed so you don't have to figure out rows and columns
byte S1[64]={  14, 0,  4,  15, 13, 7,  1,  4,  2,  14, 15, 2,  11, 13, 8,  1,  3,  10, 10, 6,  6,  12, 12, 11, 5,  9,  9,  5,  0,  3,  7,  8,  4,  15, 1,  12, 14, 8,  8,  2,  13, 4,  6,  9,  2,  1,  11, 7,  15, 5,  12, 11, 9,  3,  7,  14, 3,  10, 10, 0,  5,  6,  0,  13, };
byte S2[64]={  15, 3,  1,  13, 8,  4,  14, 7,  6,  15, 11, 2,  3,  8,  4,  14, 9,  12, 7,  0,  2,  1,  13, 10, 12, 6,  0,  9,  5,  11, 10, 5,  0,  13, 14, 8,  7,  10, 11, 1,  10, 3,  4,  15, 13, 4,  1,  2,  5,  11, 8,  6,  12, 7,  6,  12, 9,  0,  3,  5,  2,  14, 15, 9,  };
byte S3[64]={  10, 13, 0,  7,  9,  0,  14, 9,  6,  3,  3,  4,  15, 6,  5,  10, 1,  2,  13, 8,  12, 5,  7,  14, 11, 12, 4,  11, 2,  15, 8,  1,  13, 1,  6,  10, 4,  13, 9,  0,  8,  6,  15, 9,  3,  8,  0,  7,  11, 4,  1,  15, 2,  14, 12, 3,  5,  11, 10, 5,  14, 2,  7,  12, };
byte S4[64]={  7,  13, 13, 8,  14, 11, 3,  5,  0,  6,  6,  15, 9,  0,  10, 3,  1,  4,  2,  7,  8,  2,  5,  12, 11, 1,  12, 10, 4,  14, 15, 9,  10, 3,  6,  15, 9,  0,  0,  6,  12, 10, 11, 1,  7,  13, 13, 8,  15, 9,  1,  4,  3,  5,  14, 11, 5,  12, 2,  7,  8,  2,  4,  14, };
byte S5[64]={  2,  14, 12, 11, 4,  2,  1,  12, 7,  4,  10, 7,  11, 13, 6,  1,  8,  5,  5,  0,  3,  15, 15, 10, 13, 3,  0,  9,  14, 8,  9,  6,  4,  11, 2,  8,  1,  12, 11, 7,  10, 1,  13, 14, 7,  2,  8,  13, 15, 6,  9,  15, 12, 0,  5,  9,  6,  10, 3,  4,  0,  5,  14, 3,  };
byte S6[64]={  12, 10, 1,  15, 10, 4,  15, 2,  9,  7,  2,  12, 6,  9,  8,  5,  0,  6,  13, 1,  3,  13, 4,  14, 14, 0,  7,  11, 5,  3,  11, 8,  9,  4,  14, 3,  15, 2,  5,  12, 2,  9,  8,  5,  12, 15, 3,  10, 7,  11, 0,  14, 4,  1,  10, 7,  1,  6,  13, 0,  11, 8,  6,  13, };
byte S7[64]={  4,  13, 11, 0,  2,  11, 14, 7,  15, 4,  0,  9,  8,  1,  13, 10, 3,  14, 12, 3,  9,  5,  7,  12, 5,  2,  10, 15, 6,  8,  1,  6,  1,  6,  4,  11, 11, 13, 13, 8,  12, 1,  3,  4,  7,  10, 14, 7,  10, 9,  15, 5,  6,  0,  8,  15, 0,  14, 5,  2,  9,  3,  2,  12, };
byte S8[64]={  13, 1,  2,  15, 8,  13, 4,  8,  6,  10, 15, 3,  11, 7,  1,  4,  10, 12, 9,  5,  3,  6,  14, 11, 5,  0,  0,  14, 12, 9,  7,  2,  7,  2,  11, 1,  4,  14, 1,  7,  9,  4,  12, 10, 14, 8,  2,  13, 0,  15, 6,  12, 10, 9,  13, 0,  15, 3,  3,  5,  5,  6,  8,  11, };

// Takes 32 bits input, 48 bits key Kn, gives 32 bits output
// Does: P(S(Kn ^ E(R))), where R = in = R(n-1)
void F(const byte *in,const byte *Kn,byte *out)
{
  byte e[6]; // Expanded to 48 bits
  byte b1,b2,b3,b4,b5,b6,b7,b8; // Split into groups of 6 bits
  byte s[4]; // Back into 32bits after the s-box
  
  // Expand using E to 48 bits
  E(in,e);
  
  // Now XOR the output of E with the key Kn
  e[0] ^= Kn[0];
  e[1] ^= Kn[1];
  e[2] ^= Kn[2];
  e[3] ^= Kn[3];
  e[4] ^= Kn[4];
  e[5] ^= Kn[5];
  
  // Split it into 8 blocks of 6-bits
  // i: 11111111 11111111 11111111 11111111 11111111 11111111
  // e:  0           1       2        3         4       5
  // b: 11111122 22223333 33444444 55555566 66667777 77888888    
  b1 = e[0]>>2;
  b2 = ((e[0]&3)<<4) + (e[1]>>4);
  b3 = ((e[1]&15)<<2) + (e[2]>>6);
  b4 = e[2]&63;
  b5 = e[3]>>2;
  b6 = ((e[3]&3)<<4) + (e[4]>>4);
  b7 = ((e[4]&15)<<2) + (e[5]>>6);
  b8 = e[5]&63;
  
  // Now do the 'S box' lookup and return it to 32 bits
  s[0] = (S1[b1]<<4) + S2[b2];
  s[1] = (S3[b3]<<4) + S4[b4];
  s[2] = (S5[b5]<<4) + S6[b6];
  s[3] = (S7[b7]<<4) + S8[b8];
  
  // Now do final P permutation
  P(s,out);
}

// Does 1 left shift as per the CnDn
// Eg:
// in:  C0 = 11110000 11001100 10101010 1111
//      D0 =                                0101 01010110 01100111 10001111
//           [0]      [1]      [2]      [3]      [4]      [5]      [6]
// out: C1 = 11100001 10011001 01010101 1111
//      D1 =                                1010 10101100 11001111 00011110
//           [0]      [1]      [2]      [3]      [4]      [5]      [6]
// out: 11100001 10011001 01010101 11111010 10101100 11001111 00011110
//         e1      99        55       fa     ac         cf       1e
void cd_left_shift1(const byte *in,byte *out)
{
  // C
  out[0]=(in[0]<<1) + (in[1]>>7);
  out[1]=(in[1]<<1) + (in[2]>>7);
  out[2]=(in[2]<<1) + (in[3]>>7);
  // 1 nibble each C / D
  out[3]=
    ((in[3]&0xf0)<<1) + ((in[0]>>7)<<4) + // the C nibble
    ((in[3]&7)<<1) + (in[4]>>7); // the D nibble
  // D
  out[4]=(in[4]<<1) + (in[5]>>7);
  out[5]=(in[5]<<1) + (in[6]>>7);
  out[6]=(in[6]<<1) + ((in[3]>>3)&1);
}

// Eg In:
// C2 = 11000011 00110010 10101011 1111
// D2 =                                0101 01011001 10011110 00111101
//        [0]      [1]      [2]      [3]      [4]      [5]      [6]
// Out:
// C3 = 00001100 11001010 10101111 1111
// D3 =                                0101 01100110 01111000 11110101
// 
void cd_left_shift2(const byte *in,byte *out)
{
  // C
  out[0]=(in[0]<<2) + (in[1]>>6);
  out[1]=(in[1]<<2) + (in[2]>>6);
  out[2]=(in[2]<<2) + (in[3]>>6);
  // 1 nibble each C / D
  out[3]=
    ((in[3]&0xf0)<<2) + ((in[0]>>6)<<4) + // the C nibble
    ((in[3]&3)<<2) + (in[4]>>6); // the D nibble
  // D
  out[4]=(in[4]<<2) + (in[5]>>6);
  out[5]=(in[5]<<2) + (in[6]>>6);
  out[6]=(in[6]<<2) + ((in[3]>>2)&3);
}

// Takes a 64-bit message and key
// If encrypt=1 it encrypts, otherwise decrypts
// Outputs 64 bits to out
void DES(byte *m, byte *k, int encrypt, byte*out)
{
  typedef struct cd { // C and D sides of a subkey together in one structure
    byte bytes[7];
  } cd; 
  typedef struct kn { // A single subkey  
    byte bytes[6];
  } kn;
  cd cds[16];    // The Cd sSuch that C0D0 = k56, C1D1=cds[0], C16D16=cds[15]
  kn keys_k[16]; // The Kn keys output from PC2, Such that K1 = keys_k[0], etc
  int perm_i;    // Counter for making the Kn keys
  byte k56[7];   // The PC1 permutation
  byte ip[8];    // Output of performing the IP on m
  byte lold[4],rold[4]; // The previous left and right sides of the current state
  byte lnew[4],rnew[4]; // The new l & r sides of the state
  int f_i; // To keep track of the iterations and their order
  byte RLfinal[8]; // The final reversed order of the sides after the 16 iterations

  // Step 1: Create 16 subkeys, each of which is 48-bits long
  
  // Get the 56-bit PC1 permutation
  PC1(k,k56);

  // Do the left shifts
  cd_left_shift1(k56, cds[0].bytes); // Iteration 1
  cd_left_shift1(cds[0].bytes, cds[1].bytes); // Iter 2
  cd_left_shift2(cds[1].bytes, cds[2].bytes); // Iter 3
  cd_left_shift2(cds[2].bytes, cds[3].bytes); // Iter 4
  cd_left_shift2(cds[3].bytes, cds[4].bytes); // Iter 5
  cd_left_shift2(cds[4].bytes, cds[5].bytes); // Iter 6
  cd_left_shift2(cds[5].bytes, cds[6].bytes); // Iter 7
  cd_left_shift2(cds[6].bytes, cds[7].bytes); // Iter 8
  cd_left_shift1(cds[7].bytes, cds[8].bytes); // Iter 9
  cd_left_shift2(cds[8].bytes, cds[9].bytes); // Iter 10
  cd_left_shift2(cds[9].bytes, cds[10].bytes); // Iter 11
  cd_left_shift2(cds[10].bytes, cds[11].bytes); // Iter 12
  cd_left_shift2(cds[11].bytes, cds[12].bytes); // Iter 13
  cd_left_shift2(cds[12].bytes, cds[13].bytes); // Iter 14
  cd_left_shift2(cds[13].bytes, cds[14].bytes); // Iter 15
  cd_left_shift1(cds[14].bytes, cds[15].bytes); // Iter 16
  
  // Form the Keys Kn (1<=n<=16) by applying permutation PC2
  for (perm_i=0;perm_i<16;perm_i++) // Do the PC2 perms
    PC2(cds[perm_i].bytes,keys_k[perm_i].bytes);
  
  // Step 2: Encode each 64-bit block of data
  IP(m,ip);
  
  // Split it left and right
  memcpy (lold,ip,4);
  memcpy (rold,ip+4,4);

  // 16 Iterations
  if (encrypt) {
      // Encrypting
      for (f_i=0; f_i<16; f_i++)
      {
          // Ln = Rn-1
          memcpy(lnew,rold,4); 
          // Rn = Ln-1 ^ F(Rn-1,Kn)
          F(rold,keys_k[f_i].bytes,rnew); // F(Rn-1,Kn)
          rnew[0] ^= lold[0]; // ^ Ln-1
          rnew[1] ^= lold[1]; 
          rnew[2] ^= lold[2]; 
          rnew[3] ^= lold[3];
          // Copy the new values to the old ones for next iteration
          memcpy(lold,lnew,4);
          memcpy(rold,rnew,4);
      }
  } else {
      // Decrypting
      for (f_i=15; f_i>=0; f_i--)
      {
          // Ln = Rn-1
          memcpy(lnew,rold,4); 
          // Rn = Ln-1 ^ F(Rn-1,Kn)
          F(rold,keys_k[f_i].bytes,rnew); // F(Rn-1,Kn)
          rnew[0] ^= lold[0]; // ^ Ln-1
          rnew[1] ^= lold[1]; 
          rnew[2] ^= lold[2]; 
          rnew[3] ^= lold[3];
          // Copy the new values to the old ones for next iteration
          memcpy(lold,lnew,4);
          memcpy(rold,rnew,4);
      }
  }

  // Reverse the orders for the final block
  memcpy(RLfinal,rnew,4);
  memcpy(RLfinal+4,lnew,4);
  
  // Apply final perm
  IPreverse(RLfinal,out);
}
void DesEncrypt(byte *m, byte *k, byte*out)
{
  DES(m,k,1,out);
}
void DesDecrypt(byte *m, byte *k, byte*out)
{
  DES(m,k,0,out);
}

// Apply a variant in-place to a key 
// k is the key, len is the length in bytes of the key
void ApplyVariant(byte *k, int len, byte variantA, byte variantB)
{
  int i;
  for (i=0;i<len;i++)
    k[i] ^= ((i%2==0) ? variantA : variantB);
}

// Output a key (or any smallish buffer) onto screen as hex
void ShowHex(byte* b,int len,char* label)
{
  char out[100];
  int i;
  for (i=0;i<len;i++)
    sprintf(out+i*2,"%02x",b[i]);

  printf("%s%s\r\n",label, out);
}

// Encrypts the message under CBC mode
// Message length must be a multiple of 64 bits (8 bytes)
// Key must be 128 bits (16 bytes)
// Output must be the same length as the input
void TripleDesEncryptCBC(byte *m, int msg_len, byte *k, byte *out)
{
  int i,j,blocks = msg_len/8;
  byte temp1[8],temp2[8],temp3[8];
  byte vector[8]={0,0,0,0,0,0,0,0}; // init vector is all 0's
  for (i=0;i<blocks;i++)
  {
    // CBC mode: each block of plaintext is XORed with the previous ciphertext block
    for (j=0;j<8;j++)
      temp1[j] = m[i*8+j] ^ vector[j];
    // Crypto this block
    DesEncrypt(temp1,k,temp2);
    DesDecrypt(temp2,k+8,temp3);
    DesEncrypt(temp3,k,out + i*8);
    // For next block, the results of this block are the CBC vector
    memcpy(vector,out+i*8,8); 
  }
}

// Decrypts a multi-block message in CBC mode
void TripleDesDecryptCBC(byte *m, int msg_len, byte *k, byte *out)
{
  int i,j,blocks = msg_len/8;
  byte temp1[8],temp2[8],temp3[8];
  byte vector[8]={0,0,0,0,0,0,0,0}; // init vector is all 0's
  for (i=0;i<blocks;i++)
  {
    // Crypto this block
    DesDecrypt(m+i*8,k,temp1);
    DesEncrypt(temp1,k+8,temp2);
    DesDecrypt(temp2,k,temp3);

    // CBC mode: each block of plaintext is XORed with the previous ciphertext block
    for (j=0;j<8;j++)
      out[i*8+j] = temp3[j] ^ vector[j];
    
    // For next block, the crypto of this block are the CBC vector
    memcpy(vector,m+i*8,8); 
  }
}

// Test Triple DES (2-block CBC, with variant key)
int main()
{
  // Encrypt:
  // Key 68ADDFD661150E8C1C102F6BA2A8754A 
  // Variant 44c0
  // Mode CBC
  // Data BF54499D8F3E8A49A134BC5875C14679
  // This should result in: 11B96C137EF10B7F5343E70402E0A7F3

  byte k_3des[16] = {0x68,0xAD,0xDF,0xD6,0x61,0x15,0x0E,0x8C, 0x1C,0x10,0x2F,0x6B,0xA2,0xA8,0x75,0x4A};
  byte m_3des[16] = {0xBF,0x54,0x49,0x9D,0x8F,0x3E,0x8A,0x49, 0xA1,0x34,0xBC,0x58,0x75,0xC1,0x46,0x79};
  byte encrypted[16], decrypted[16];

  printf("Test Triple DES (2-block CBC, with variant key)\r\n\n");

  ShowHex(k_3des,16,"Key:         ");
  ApplyVariant(k_3des,16,0x44,0xC0);
  ShowHex(k_3des,16,"Variant key: ");
  ShowHex(m_3des,16,"Original:    ");
  TripleDesEncryptCBC(m_3des,sizeof(m_3des),k_3des,encrypted);
  ShowHex(encrypted,16,"Encrypted:   ");
  TripleDesDecryptCBC(encrypted,sizeof(encrypted),k_3des,decrypted);
  ShowHex(decrypted,16,"Decrypted:   ");

  return 0;
}
