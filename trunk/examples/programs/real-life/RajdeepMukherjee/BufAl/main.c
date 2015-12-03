/*###############################
## Author:  Rajdeep Mukherjee ##
## Date:    6/7/2015          ##
## Task:    Buffer Allocation ##
###############################*/

_Bool nondet_bool() {
  _Bool x;
  return x;
}

unsigned char nondet_uchar() {
  unsigned char x;
  return x;
}

struct state_elements_main{
  _Bool alloc;
  _Bool free;
  unsigned char free_addr;
  _Bool busy[16];
  unsigned char count;
};
struct state_elements_main  smain;

void initial() {
	smain.busy[0] = 0;
	smain.busy[1] = 0;
	smain.busy[2] = 0;
	smain.busy[3] = 0;
	smain.busy[4] = 0;
	smain.busy[5] = 0;
	smain.busy[6] = 0;
	smain.busy[7] = 0;
	smain.busy[8] = 0;
	smain.busy[9] = 0;
	smain.busy[10] = 0;
	smain.busy[11] = 0;
	smain.busy[12] = 0;
	smain.busy[13] = 0;
	smain.busy[14] = 0;
	smain.busy[15] = 0;
	smain.count = 0;
	smain.alloc = 0;
	smain.free = 0;
	smain.free_addr = 0;
}

void design(_Bool clock, _Bool alloc_raw, _Bool *nack, unsigned char *alloc_addr, _Bool free_raw, unsigned char free_addr_raw)
{
  int i;
  unsigned char tmpaddr, tmp;
  
  // always clocked block
  tmpaddr = smain.free_addr & 0xF;
  smain.count = ((smain.count & 0x1F) + (smain.alloc & !(*nack)) - (smain.free & smain.busy[tmpaddr])) & 0x1F;
  if(smain.free) smain.busy[smain.free_addr] = 0;
  tmp = *alloc_addr;
  if(smain.alloc & !nack) smain.busy[tmp] = 1;

  smain.alloc = alloc_raw;
  smain.free = free_raw;
  smain.free_addr = free_addr_raw;
  
  // continuous assignment statements
  *nack = smain.alloc && ((smain.count & 0x1F) == 16);

    *alloc_addr =
		       !smain.busy[0] ? 0 :
		       !smain.busy[1] ? 1 :
		       !smain.busy[2] ? 2 :
		       !smain.busy[3] ? 3 :
		       !smain.busy[4] ? 4 :
		       !smain.busy[5] ? 5 :
		       !smain.busy[6] ? 6 :
		       !smain.busy[7] ? 7 :
		       !smain.busy[8] ? 8 :
		       !smain.busy[9] ? 9 :
		       !smain.busy[10] ? 10 :
		       !smain.busy[11] ? 11 :
		       !smain.busy[12] ? 12 :
		       !smain.busy[13] ? 13 :
		       !smain.busy[14] ? 14 :
		       !smain.busy[15] ? 15 : 0;

}
void main() {
  _Bool clock;
  _Bool alloc_raw;
  _Bool nack;
  unsigned char alloc_addr;
  _Bool free_raw;
  unsigned char free_addr_raw;
  int i=0;
  initial();
  while(1) {
   alloc_raw = nondet_bool();
   free_raw = nondet_bool();
   free_addr_raw = nondet_uchar();
   design(clock, alloc_raw, &nack, &alloc_addr, free_raw, free_addr_raw);
   if (!((((smain.count >> 4) & 1) == 0) || ((smain.count & 0xF) == 0))) {
       //@ assert \false;
   }
  }
}
