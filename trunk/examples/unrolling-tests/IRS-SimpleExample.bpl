var input1 : int;
var input2 : int;
var output1 : int;
var output2 : int;

procedure Main();

implementation Main()
{
  var timer_10 : int;
  var timer_100 : int;
  
  timer_10 := 0;
  timer_100 := 0;
   
  while(true){
  
	if(timer_10 == 10){
		if(input1 != 1){
			output1 := 1;
		} else {
			output1 := 0;
		}
		timer_10 := 0;
	}
	
	if(timer_100 == 100){
		if(input2 != 1){
			output2 := 1;
		} else {
			output2 := 0;
		}
		timer_100 := 0;
	}
	
	timer_10 := timer_10 + 1;
	timer_100 := timer_100 + 1;
	
  }
}