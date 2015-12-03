#include <stdio.h>
#include <assert.h>

_Bool nondet_bool();
unsigned char nondet_uchar();

int MSBD = 3;
int LAST = 15;
int MSBA = 3;

struct state_elements_srFIFO {
  _Bool empty;
  unsigned char mem[16];
  unsigned char tail;
};
struct state_elements_srFIFO  ssrFIFO;

void initial_srFIFO() {
  int i;
  for(i = 0; i <= LAST; i = i + 1)
    ssrFIFO.mem[i] = 0;
  ssrFIFO.tail = 0;
  ssrFIFO.empty = 1;
} 

void srFIFO(_Bool clock, unsigned char dataIn, _Bool push, _Bool pop, unsigned char *dataOut, _Bool *full, _Bool *empty)
{
  int i;
  unsigned char tmp1;
  // clocked block 
  if(push && !*full)
  {
    for(i = LAST; i > 0; i = i - 1)
      ssrFIFO.mem[i] = (ssrFIFO.mem[i - 1] & 0xF);
    ssrFIFO.mem[0] = dataIn & 0xF;
    
    if(!ssrFIFO.empty)
      ssrFIFO.tail = (ssrFIFO.tail + 1) & 0xF;
    ssrFIFO.empty = 0;
    *empty = 0;
  }

  else
    if(pop && !ssrFIFO.empty)
    {
      if(ssrFIFO.tail == 0)
      {
        ssrFIFO.empty = 1;
        *empty = 1;
      }
    else
        ssrFIFO.tail = ((ssrFIFO.tail & 0xF) - 1) & 0xF;
    }

  tmp1 = ssrFIFO.tail & 0xF;
  *dataOut = (ssrFIFO.mem[tmp1]) & 0xF;
  *full = ((ssrFIFO.tail & 0xF) == LAST);
}

struct state_elements_rbFIFO{
  _Bool empty;
  unsigned char mem[16];
  unsigned char head;
  unsigned char tail;
};
struct state_elements_rbFIFO  srbFIFO;

void initial_rbFIFO()
{
  int i;
  for(i = 0;i <= LAST; i = i + 1)
    srbFIFO.mem[i] = 0;
  srbFIFO.head = 0;
  srbFIFO.tail = 0;
  srbFIFO.empty = 1;
}

void rbFIFO(_Bool clock, unsigned char dataIn, _Bool push, _Bool pop, unsigned char *dataOut, _Bool *full, _Bool *empty)
{
  unsigned char tmp1, tmp2; 
  
  if(push && !*full)
  {
    tmp1 = srbFIFO.head & 0xF;
    srbFIFO.mem[tmp1] = dataIn & 0xF;
    srbFIFO.head = ((srbFIFO.head & 0xF) + 1) & 0xF;
    srbFIFO.empty = 0;
    *empty = 0;
  }

  else
    if(pop && !srbFIFO.empty)
    {
      srbFIFO.tail = ((srbFIFO.tail & 0xf) + 1) & 0xF;
      if((srbFIFO.tail & 0xF) == (srbFIFO.head & 0xF)) {
        srbFIFO.empty = 1;
        *empty = 1;
      }
    }
  tmp2 = srbFIFO.tail & 0xF;
  *dataOut = (srbFIFO.mem[tmp2]) & 0xF;
  *full = ((srbFIFO.tail & 0xF) == (srbFIFO.head & 0xF)) & (!srbFIFO.empty );
}

unsigned char srDataOut;
_Bool srFull;
_Bool srEmpty;
unsigned char rbDataOut;
_Bool rbFull;
_Bool rbEmpty;

_Bool design(_Bool clock, unsigned char dataIn, _Bool push, _Bool pop, _Bool *equal)
{
  
  srFIFO(clock, dataIn, push, pop, &srDataOut, &srFull, &srEmpty);
  rbFIFO(clock, dataIn, push, pop, &rbDataOut, &rbFull, &rbEmpty);
  // the below should fail
  *equal = ((srFull == rbFull) && (ssrFIFO.empty == srbFIFO.empty) && (ssrFIFO.empty || (srDataOut == rbDataOut)));
  if (srFull != rbFull) {
	  //@ assert \false;
  }
  if(srEmpty != rbEmpty) {
	  //@ assert \false;
  }
  if(*equal != 1) {
	  //@ assert \false;
  }
}


void main() {
  _Bool clock;
  unsigned char dataIn;
  _Bool push;
  _Bool pop;
  _Bool equal;

  initial_rbFIFO();
  initial_srFIFO();
  
  while(1) {
    push = nondet_bool();
    pop = nondet_bool();
    dataIn = nondet_uchar();
    design(clock, dataIn, push, pop, &equal);
  }
}
