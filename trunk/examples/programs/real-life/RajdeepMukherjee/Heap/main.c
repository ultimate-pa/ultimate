#include <stdio.h>
#define TRUE 1
#define FALSE 0

unsigned char nondet_uchar();

struct state_elements_main{
  unsigned char h2;
  _Bool error;
  unsigned char h[4];
  unsigned char state;
  unsigned char nitems;
  unsigned char posn;
  unsigned char h0;
  unsigned char h1;
};
struct state_elements_main  smain;

// parameter declaration
int BITS = 2;
int WORDS = 4;
int MSW = 3;
int MSB = 1;
int NOOP = 0;
int PUSH = 1;
int POP = 2;
int TEST = 3;
int IDLE = 0;
int PUSH1 = 1;
int PUSH2 = 2;
int POP1 = 3;
int POP2 = 4;
int POP3 = 5;
int TEST1 = 6;
int TEST2 = 7;

void initial(_Bool clock, unsigned char cmd, unsigned char din, unsigned char *dout, _Bool *ready, _Bool *full, _Bool *empty, _Bool *error) {
  int j;
  smain.state = IDLE;
  smain.nitems = 0;
  smain.posn = 0;
  smain.h0 = 0;
  smain.h1 = 0;
  smain.h2 = 0;
  smain.error = FALSE;
  *error = FALSE;
  for(j = 0; j < WORDS; j = j + 1)
    smain.h[j] = 0;
}


void heap(_Bool clock, unsigned char cmd, unsigned char din, unsigned char *dout, _Bool *ready, _Bool *full, _Bool *empty, _Bool *error)
{
  //wire declarations
  unsigned char prnt;
  unsigned char lft;
  unsigned char rght;
 
  *dout = smain.h[0]&3;
  *dout = smain.h[0]&3;
  *ready = (smain.state == IDLE);
  *ready = (smain.state == IDLE);
  *full = (smain.nitems == WORDS);
  *full = (smain.nitems == WORDS);
  *empty = (smain.nitems == 0);
  *empty = (smain.nitems == 0);
    
 
    if(smain.state == IDLE)
    {
      if(cmd == PUSH) {
        if(full == 0)
        {
          smain.posn = smain.nitems&7;
          smain.h0 = din&3;
          smain.nitems = ((smain.nitems&7) + 1)&3;
          smain.state = PUSH1;
        }

      else
        if(cmd == POP)
          if(empty == 0)
          {
            smain.nitems = (((smain.nitems)&7) - 1)&3;
            smain.posn = 0;
            smain.h0 = (smain.h[(smain.nitems & 7)])&3;
            smain.h[0] = smain.h0&3;
            smain.state = POP1;
          }
        else
          if(cmd == TEST)
          {
            smain.posn = 1;
            smain.error = FALSE;
            *error = FALSE;
            smain.state = TEST1;
          }
          else
            if(cmd == NOOP)
            {
            }

      } // end of cmd
    } // end of IDLE
    else
      if(smain.state == PUSH1)
      {
        smain.h1 = (smain.h[prnt&7])&3;
        smain.state = PUSH2;
      }
      else
        if(smain.state == PUSH2) {
          if(smain.posn == 0 || (smain.h1 <= smain.h0))
          {
            smain.h[(smain.posn&7)] = smain.h0 & 3;
            smain.state = IDLE;
          }
          else
          {
            smain.h[(smain.posn&7)] = smain.h1 & 3;
            smain.posn = prnt & 7;
            smain.state = PUSH1;
          }
        }
        else
          if(smain.state == POP1)
          {
            smain.h1 = smain.h[(lft&7)] & 3;
            smain.state = POP2;
          }
          else
            if(smain.state == POP2)
            {
              smain.h2 = smain.h[(rght & 7)] & 3;
              smain.state = POP3;
            }
            else
              if(smain.state == POP3)
              {
                if(lft < smain.nitems && smain.h1 < smain.h0 && (rght >= smain.nitems || smain.h1 <= smain.h2))
                {
                  smain.h[(smain.posn & 7)] = smain.h1 & 3;
                  smain.posn = lft & 7;
                  smain.state = POP1;
                }

                else
                  if(rght < smain.nitems && smain.h2 < smain.h0)
                  {
                    smain.h[(smain.posn & 7)] = smain.h2 & 3;
                    smain.posn = rght & 7;
                    smain.state = POP1;
                  }
                  else
                  {
                    smain.h[(smain.posn & 7)] = smain.h0 & 3;
                    smain.state = IDLE;
                  }
              }
              else
                if(smain.state == TEST1) {
                  if(smain.posn >= smain.nitems)
                  {
                    smain.state = IDLE;
                  }
                  else
                  {
                    smain.h1 = smain.h[(prnt & 7)] & 3;
                    smain.state = TEST2;
                  }
                }
                else
                  if(smain.state == TEST2) {
                    if(smain.h[(smain.posn) & 7] < smain.h1) {
                        smain.error = TRUE;
                        *error = TRUE;
                      smain.state = IDLE;
                    }
                    else
                    {
                      smain.posn = ((smain.posn & 7) + 1) & 7;
                      smain.state = TEST1;
                    }
               }
       
  unsigned char tmp;
  tmp = ((smain.posn & 7) - 1) & 7;
  prnt = (0 << 2 || ((tmp>>1)&3));
  lft = ((((smain.posn & 3)<<1) || 0) + 1)&7;
  unsigned char tmp1;
  tmp1 = ((smain.posn & 7) + 1) & 7;
  rght = (((tmp1&3)<<1) || 0)&7;
  
}

void main() {
  _Bool clock;
  unsigned char cmd;
  unsigned char din;
  unsigned char dout;
  _Bool ready;
  _Bool full;
  _Bool empty;
  _Bool error;

  initial(clock, cmd, din, &dout, &ready, &full, &empty, &error);
  
  while(1) {
    cmd = nondet_uchar();
    din = nondet_uchar();  
    heap(clock, cmd, din, &dout, &ready, &full, &empty, &error);
   
    //#PASS: The heap property is never violated.
    if(error!=0) {
		//@ assert \false;
	}
 
    //#PASS: the number of items is always between 0 and 4.
    if(!((((smain.nitems>>2)&1)==0) || ((smain.nitems&3)==0))) {
		//@ assert \false;
  }
  }
}
