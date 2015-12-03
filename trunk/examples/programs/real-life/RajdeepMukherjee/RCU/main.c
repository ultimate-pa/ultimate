// ******************************************************************
// Model for the RCU (read-copy update) mutual exclusion mechanism. *
// This model assumes one update process.                           *
// Promela Author: Paul McKenney                                    *
// Verilog Author:  Fabio Somenzi                                   *
// C Author:  Rajdeep Mukherjee                                     *
// ****************************************************************** 

#include <stdio.h>
#include <assert.h>
#define TRUE 1
#define FALSE 0

unsigned char nondet_uchar();
// parameter definition 
  int PASSES = 10;
  int NRDR = 4; // number of reader process
  int NRDR_ELEM = 8;
  int SELMSB = 2; // MSB for select input 
  int L0 = 0;
  int L1 = 1;
  int L2 = 2;
  int L3 = 3;
  int L4 = 4;
  int L5 = 5;
  int L6 = 6;
  int L7 = 7;
  int L8 = 8;
  int L9 = 9;
  int L10 = 10;

struct state_elements_main {
 _Bool flip;
 _Bool ctr[8];
 unsigned char passctr;

 // latched version of select, to which we can refer in properties
 unsigned char self;

 // local variables for the reader process
 unsigned char pc[4];
 _Bool lclFlip[4];
 _Bool both[4];
 
 // local variables for the update process
 unsigned char cpunum;
 unsigned char lclPassctr;
 unsigned char pcu;
};

struct state_elements_main  smain;

void rcu(_Bool clock, unsigned char select)
{
  int i;
  
  // clocked block with blocking assignments
  smain.self = select;
  if(smain.self >= NRDR)
  {
      if((unsigned int)smain.pcu == L0) {
        if((unsigned int)smain.passctr < PASSES)
        {
          smain.lclPassctr = smain.passctr;
          smain.pcu = L1;
        }
      }
      else if((unsigned int)smain.pcu == L1)
      {
        if(!(smain.lclPassctr & 1))
          smain.lclPassctr = 255;
        smain.pcu = L2;
      }
      else if((unsigned int)smain.pcu == L2)
      {
         smain.cpunum = 0;
         smain.pcu = L3;
      }
      else if((unsigned int)smain.pcu == L3) {
        if((unsigned int)smain.cpunum < NRDR)
           smain.pcu = L4;
        else
           smain.pcu = L6;
      }
      else if((unsigned int)smain.pcu == L4) {
        unsigned int concat = ((smain.cpunum & 7) << 1) | !(smain.flip & 1);
        if (smain.ctr[concat] == 0)
           smain.pcu = L5;
      }
      else if((unsigned int)smain.pcu == L5)
      {
           smain.cpunum = smain.cpunum + 1;
           smain.pcu = L3;
      }
      else if((unsigned int)smain.pcu == L6)
      {
           smain.flip = !smain.flip;
           smain.pcu = L7;
      }
      else if((unsigned int)smain.pcu == L7)
      {
           smain.cpunum = 0;
           smain.pcu = L8;
      }
      else if((unsigned int)smain.pcu == L8) {
        if((unsigned int)smain.cpunum < NRDR)
           smain.pcu = L9;
        else
          smain.pcu = L0;
     }
     else if((unsigned int)smain.pcu == L9) {
        unsigned int concat = ((smain.cpunum & 7) << 1) | !(smain.flip & 1);
        if (smain.ctr[concat] == 0)
           smain.pcu = L10;
     }
     else if((unsigned int)smain.pcu == L10)
     {
         smain.cpunum = smain.cpunum + 1;
         smain.pcu = L8;
     }
  } // end of if

  else
  {
    if((unsigned int)smain.pc[(unsigned char)smain.self] == L0) {
      if((unsigned int)smain.passctr < PASSES)
      {
        smain.lclFlip[(unsigned char)smain.self] = smain.flip;
        smain.pc[(unsigned char)smain.self] = L1;
      }
    }
    else if((unsigned int)smain.pc[(unsigned char)smain.self] == L1)
    {
      unsigned int concatright = ((smain.self & 7) << 1) | ((smain.lclFlip[smain.self] & 1) << 0); 
      unsigned int concatleft = ((smain.self & 7) << 1) | ((smain.lclFlip[smain.self] & 1) << 0); 
      smain.ctr[concatleft] = ~smain.ctr[concatright]; 
      smain.pc[(unsigned char)smain.self] = L2;
    }
    else if((unsigned int)smain.pc[(unsigned char)smain.self] == L2) {
      if(smain.lclFlip[(unsigned char)smain.self] == smain.flip)
      {
        smain.both[(unsigned char)smain.self] = FALSE;
        smain.pc[(unsigned char)smain.self] = L4;
      }
      else
      {
        unsigned int concatright = ((smain.self & 7) << 1) | !((smain.lclFlip[smain.self] & 1) << 0); 
        unsigned int concatleft = ((smain.self & 7) << 1) | !((smain.lclFlip[smain.self] & 1) << 0); 
        smain.ctr[concatleft] = ~smain.ctr[concatright]; 
        smain.pc[(unsigned char)smain.self] = L3;
      }
    }
   else if((unsigned int)smain.pc[(unsigned char)smain.self] == L3)
   {
     smain.both[(unsigned char)smain.self] = TRUE;
     smain.pc[(unsigned char)smain.self] = L4;
   }
   else if((unsigned int)smain.pc[(unsigned char)smain.self] == L4)
   {
     smain.passctr = (unsigned char)(unsigned int)smain.passctr + 1;
     smain.pc[(unsigned char)smain.self] = L5;
   }
   else if((unsigned int)smain.pc[(unsigned char)smain.self] == L5)
   {
     smain.passctr = (unsigned char)(unsigned int)smain.passctr + 1;
     smain.pc[(unsigned char)smain.self] = L6;
   }
   else if((unsigned int)smain.pc[(unsigned char)smain.self] == L6)
   {
     unsigned int concatright = ((smain.self & 7) << 1) | ((smain.lclFlip[smain.self] & 1) << 0); 
     unsigned int concatleft = ((smain.self & 7) << 1) | ((smain.lclFlip[smain.self] & 1) << 0); 
     smain.ctr[concatleft] = ~smain.ctr[concatright]; 
     smain.pc[(unsigned char)smain.self] = L7;
   }
   else if((unsigned int)smain.pc[(unsigned char)smain.self] == L7)
   {
     if(smain.both[(unsigned char)smain.self]) {
       unsigned int concatright = ((smain.self & 7) << 1) | !((smain.lclFlip[smain.self] & 1) << 0); 
       unsigned int concatleft = ((smain.self & 7) << 1) | !((smain.lclFlip[smain.self] & 1) << 0); 
       smain.ctr[concatleft] = ~smain.ctr[concatright]; 
     }  
     smain.pc[(unsigned char)smain.self] = L0;
   }
 } // end of else
}  // end of rcu

void initial() {
  
  // register initialization
  smain.flip = FALSE;
  smain.passctr = 0;
  smain.cpunum = 0;
  
  unsigned int i;
  for(i = 0; i < NRDR_ELEM; i = i + 1)
    smain.ctr[i] = FALSE;
  for(i = 0; i < NRDR; i = i + 1)
  {
    smain.lclFlip[i] = FALSE;
    smain.both[i] = FALSE;
    smain.pc[i] = L0;
  }
  smain.pcu = L0;
  smain.self = 0;
  smain.lclPassctr = 0;
}

int main() {
  _Bool clock;
  unsigned char select; // non-deterministic scheduler
  // Initialization
  initial();
  
  while(1) {
   
   select = nondet_uchar(); // non-deterministic scheduler
   // call rcu 
   rcu(clock, select);
   
   // check safety invariant properties
   
   // *********************** Property 1 *******************************
   // G((pcu=L8 * cpunum[2:0]=4) -> !(lclPassctr[7:0] == passctr[7:0]));
   // ******************************************************************
   if(!((!((smain.pcu == L8) && ((smain.cpunum & 0x7) == 4))) || (!((smain.lclPassctr & 0xff) == (smain.passctr & 0xff))))) {
	  //@ assert \false;
  }
 
   // *********************** Property 2 *******************************
   //                      G lclPassctr[7:4]={0,15};
   // ******************************************************************
   if(!( (((smain.lclPassctr >> 4) & 0xf) == 0) || (((smain.lclPassctr >> 4) & 0xf) == 15) )) {
	  //@ assert \false;
  }
 } // end of while(1)
 return 1;
} // end of main
