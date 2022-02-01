//#Unsafe
//@ ltl invariant someinv: !([](AP(timer_1 == 0) ==> <>(AP(output_1 == 1))));

int timer_1;
int output_1;
	
void run_timer(){
	timer_1++;
	if(timer_1>=10){
		timer_1=0;
	}
}

void main()
{
	timer_1 = 0;
	output_1 = 0;

    while(1){
		run_timer();
		
		if(timer_1==0){
			output_1=1;
		} else{
			output_1=0;
		}
    }
}