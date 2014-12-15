//#Unsafe
//@ ltl invariant someinv: !([](AP(x == 0) ==> <>(AP(y == 1))));

int x=0;
int y=0;
	
void foo(){
	x++;
	if(x>=10){
		x=0;
	}
}

void main()
{
    while(1){
		foo();
		
		if(x==0){
			y=1;
		} else{
			y=0;
		}
    }
}