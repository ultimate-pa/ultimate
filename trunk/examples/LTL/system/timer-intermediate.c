//#Safe
//@ ltl invariant someinv: ([](AP(input_1 < 1000) ==> <>(AP(output_1 == 1))));

extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int timer_1;
int timer_2;

int input_1;
int output_1;
int aux = 0;
	
void run_timer(){
	timer_1++;
	if(timer_1>=2){
		timer_1=0;
		
		timer_2++;
		if(timer_2>=2){
			timer_2=0;
		}
	}
}

int read_input_1(){
	input_1 = __VERIFIER_nondet_int();
	__VERIFIER_assume(input_1 < 65535); 
	return input_1;
}

void main()
{
	timer_1 = 0;
	timer_2 = 0;
	
	output_1 = 0;
	aux = 0;

    while(1){
		run_timer();
		
		if(timer_1==0){
			if(read_input_1() < 1000){
				if(timer_2==0){
					aux++;
				}
				output_1 = 1;
			}
		} 
    }
}