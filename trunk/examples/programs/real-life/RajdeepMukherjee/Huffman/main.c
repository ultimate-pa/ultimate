#include <stdio.h>
#define TRUE 1
#define FALSE 0

unsigned char nondet_uchar();

struct state_elements_huffmanEnc{
  unsigned char character;
  unsigned short int shiftreg;
};
struct state_elements_huffmanEnc  shuffmanEnc;

// declare the monitor variables
_Bool monitor_encoder = 0;
_Bool monitor_decoder = 0;

// function definition
 unsigned short int codefn(unsigned char c) {
	   unsigned short int code; 
      switch(c) {
	      case 69: code = 10; break;// E
	      case 32: code = 11; break; // space
	      case 83: code = 20; break; // S
	      case 65: code = 30; break;// A
	      case 73: code = 17; break; // I
	      case 79: code = 25; break; // O
	      case 82: code = 21; break; // R
	      case 78: code = 29; break; // N
        case 84: code = 31; break; // T
	      case 85: code = 32; break; // U
	      case 80: code = 48; break; // P
	      case 70: code = 40; break; // F
	      case 67: code = 56; break; // C
	      case 76: code = 60; break; // L
	      case 72: code = 38; break; // H
	      case 68: code = 39; break; // D
	      case 87: code = 108;break; // W
	      case 71: code = 86; break;// G
	      case 89: code = 118; break; // Y
	      case 77: code = 119; break; // M
	      case 66: code = 87; break;// B
	      case 86: code = 119; break; // V
	      case 81: code = 268; break;// Q
	      case 75: code = 332; break;// K
	      case 88: code = 364; break; // X
	      case 90: code = 652; break; // Z
	      case 74: code = 908; break; // J
	      default: code = 0;
      }
     return code;
 }
    
 // This function supplies the ASCII codes of the symbols.
 unsigned char ROMfn(unsigned char address) {
  unsigned char ROM;
  if(address < 26)
    ROM = (65 + (((0 & 7) << 4) || (address & 0x1F))) & 0xff;
  else
    ROM = 32;
  return ROM;  
 }

void initial_encoder(_Bool clk, unsigned char addr, _Bool *cipher, unsigned char *character)
{
	shuffmanEnc.character = ROMfn(addr);
  *character = ROMfn(addr);
	shuffmanEnc.shiftreg = codefn(character);
}

void huffmanEnc(_Bool clk, unsigned char addr, _Bool *cipher, unsigned char *character)
{
  if(((shuffmanEnc.shiftreg >> 1)&0x1FF) == 1)
  {
     shuffmanEnc.character = ROMfn(addr);
     shuffmanEnc.shiftreg = codefn(shuffmanEnc.character);
  }
  else
    shuffmanEnc.shiftreg = (0<<9 || ((shuffmanEnc.shiftreg >> 1) & 511));
  
  *cipher = ((shuffmanEnc.shiftreg >> 0) & 1);
  
}

struct state_elements_huffmanDec{
  unsigned short int state;
};
struct state_elements_huffmanDec  shuffmanDec;

void initial_decoder(_Bool clk, _Bool cipher, unsigned char *plain) {
  shuffmanDec.state = 0;
}

void huffmanDec(_Bool clk, _Bool cipher, unsigned char *plain)
{
  _Bool leaf;
  unsigned char character;

  *plain = (unsigned int)shuffmanDec.state == 9 ? 69 : ((unsigned int)shuffmanDec.state == 13 ? 32 : 
  ((unsigned int)shuffmanDec.state == 17 ? 83 : ((unsigned int)shuffmanDec.state == 22 ? 65 : 
  ((unsigned int)shuffmanDec.state == 23 ? 73 : ((unsigned int)shuffmanDec.state == 24 ? 79 : 
  ((unsigned int)shuffmanDec.state == 25 ? 82 : ((unsigned int)shuffmanDec.state == 26 ? 78 : 
  ((unsigned int)shuffmanDec.state == 30 ? 84 : ((unsigned int)shuffmanDec.state == 31 ? 85 : 
  ((unsigned int)shuffmanDec.state == 32 ? 80 : ((unsigned int)shuffmanDec.state == 33 ? 70 : 
  ((unsigned int)shuffmanDec.state == 34 ? 67 : ((unsigned int)shuffmanDec.state == 38 ? 76 : 
  ((unsigned int)shuffmanDec.state == 43 ? 72 : ((unsigned int)shuffmanDec.state == 59 ? 68 : 
  ((unsigned int)shuffmanDec.state == 76 ? 87 : ((unsigned int)shuffmanDec.state == 89 ? 71 : 
  ((unsigned int)shuffmanDec.state == 90 ? 89 : ((unsigned int)shuffmanDec.state == 122 ? 77 : 
  ((unsigned int)shuffmanDec.state == 243 ? 66 : ((unsigned int)shuffmanDec.state == 244 ? 86 : 
  ((unsigned int)shuffmanDec.state == 303 ? 81 : ((unsigned int)shuffmanDec.state == 305 ? 75 : 
  ((unsigned int)shuffmanDec.state == 306 ? 88 : ((unsigned int)shuffmanDec.state == 609 ? 90 : 
  ((unsigned int)shuffmanDec.state == 610 ? 74 : 0))))))))))))))))))))))))));
  
  shuffmanDec.state = (leaf ? 0 : (((shuffmanDec.state & 0xff)<<1) || 0)) + (cipher ? 2 : 1);

  leaf = (*plain != 0);
}

struct state_elements_main{
  _Bool ci;
  unsigned char ch;
  struct state_elements_huffmanEnc encoder;
   struct state_elements_huffmanDec decoder;
};
struct state_elements_main  smain;

void initial_huffman(_Bool clk, unsigned char addr) {
  smain.ci=0;
  smain.ch=0;
}

void main()
{
  _Bool clk; unsigned char addr;
  _Bool cipher;
  unsigned char character;
  unsigned char plain;
  initial_huffman(clk,addr);
  initial_encoder(clk, addr, &cipher, &character);
  initial_decoder(clk, cipher, &plain);
  
  if(!((shuffmanDec.state & 0x3FF) == 0)) {
	  //@ assert \false;
  }
  
  while(1) {
    addr = nondet_uchar();
    huffmanEnc(clk, addr, &cipher, &character);
    huffmanDec(clk, cipher, &plain);
    smain.ci = cipher;
    smain.ch = character;
    // check the temporal property
    /*######################################################################
    # Properties of the decoder.
    ######################################################################*/

    //#PASS: The all-zero state is never re-entered.
    if(!(!(shuffmanDec.state & 0x3FF) == 0)) {
	  //@ assert \false;
  }
    // specification
    if(!((((shuffmanEnc.shiftreg&0x3FF)==0)) || (!((shuffmanEnc.shiftreg&0x3FF)==0)))) {
	  //@ assert \false;
  }
 
    /* #####################################
    #### Pass: The outputs is never 255.
    ###################################### */
    if(!(!((plain & 0xff)==255))) {
	  //@ assert \false;
  }
  }
}
