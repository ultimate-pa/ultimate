//#Safe

//@ ltl invariant positive: ( <>[] ( AP(output == 0)));

extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int output, input;

int main()
{
	output = -1;
	
    while(1)
    {
		input = __VERIFIER_nondet_int();
		
		if(input>0){
			__VERIFIER_assume(0);
		} else {
			output = 0;	
		}
    }
}
