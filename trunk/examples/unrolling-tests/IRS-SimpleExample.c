int input1 ;
int input2 ;
int output1;
int output2;

void Main(void)
{
  int timer_10;
  int timer_100;
  
  timer_10 = 0;
  timer_100 = 0;
   
  while(1){
  
	if(timer_10 == 10){
		if(input1 != 1){
			output1 = 1;
		} else {
			output1 = 0;
		}
		timer_10 = 0;
	}
	
	if(timer_100 == 100){
		if(input2 != 1){
			output2 = 1;
		} else {
			output2 = 0;
		}
		timer_100 = 0;
	}
	
	timer_10++;
	timer_100++;
	
  }
}