//#Unsafe

//@ ltl invariant positive: <>AP(output == 0) || <>AP(output == 1);

extern void __VERIFIER_assume();
extern int __VERIFIER_nondet_int();

int output, input;

int calc(int val){
	if(input == 1){
		__VERIFIER_assume(0);
	} else if(input == 2){
		output = -1;
	} else {
		output = 0;	
	}
}


int main()
{
	output = -1;
	
    while(1)
    {
		input = __VERIFIER_nondet_int();
		__VERIFIER_assume(input == 1 || input == 2 || input == 3);
		output = calc(input);
	}
}
