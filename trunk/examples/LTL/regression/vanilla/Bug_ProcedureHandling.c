//#Unsafe
//@ ltl invariant positive: AP(istemp == 0) || []AP(A != 1);

extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

void StrategyInvalidateBuffer() {}
void WaitIO() {}
int RelFileNodeEquals(int a, int b) { return __VERIFIER_nondet_int(); }

int istemp = __VERIFIER_nondet_int();
int bufHdr_tag_rnode;
int rnode;
int A;
int NLocBuffer;
int nondet;

void main() {
	//istemp = __VERIFIER_nondet_int();
	nondet = __VERIFIER_nondet_int();
	NLocBuffer = 2;
	
	A = 0;
	if (istemp==1)
	{
		 for (int i = 0; i < NLocBuffer; i++)
		{
			if (RelFileNodeEquals(bufHdr_tag_rnode, rnode))
			{
			}
		}
		goto my_exit;
	}
	
	A = 1;

	for (int i = 1; i <= NLocBuffer; i++)
	{

recheck:
		if (RelFileNodeEquals(bufHdr_tag_rnode, rnode))
		{
			if (nondet)
			{
				nondet = __VERIFIER_nondet_int();
				WaitIO(); 
				goto recheck;
			}
			StrategyInvalidateBuffer(); 
		}
	}
        
 my_exit:
	while(1) { int yyy;yyy=yyy;}
}