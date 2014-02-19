/*
Example properties:
	
	terminating [+] | nonterminating [ ] | correct [10790ms]
		String fileContent = "[](i -> (!b -> <>[]a))\n"
		+ "b: tempIn >= 0 \n"
		+ "a: error = 1\n"
		+ "i: init = 2";
		
	terminating [-] | nonterminating [-] | correct [java.lang.AssertionError: no run for summary found] | with Error 2
		String fileContent = "[](i -> (!b -> <>[]a))\n"
		+ "b: tempIn >= 0 \n"
		+ "a: error = 1\n"
		+ "i: init = 2";

	terminating [+] | nonterminating [ ] | correct [17630ms]
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 2";		
		
	terminating [ ] | nonterminating [+] | correct [4030ms] |  With Error 1
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 2";
		
		Stem: init := 0;assume true; tempDisplay := 0;assume true; warnLED := 1;assume true; tempIn := 0;assume true; error := 0;assume true; chainBroken := 0;assume true; warnLight := 0;assume true; temp := 0;assume true; time := 0;assume true; init := 1;assume true; assume true;assume true; havoc limes;assume true; assume !(limes > 10);assume true; error := 0;assume true; call display(0, error, 1);< assume true; assume onlyWarn != 0;assume true; tempDisplay := tempdiff;assume true; warnLED := warn;assume true; assume true;assume true; >return call display(0, error, 1); assume true; init := 2;assume true; call coolantControl();< assume true; assume true;assume true; time := time + 1;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume temp > 8;assume temp > 8 && init == 2; 
		Loop: chainBroken := 1;assume true; assume true;assume true; time := time + 1;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume !(temp > 8);assume true; chainBroken := 0;assume true; assume true;assume !(chainBroken == 1); time := time + 1;assume true; havoc tempIn;assume !(chainBroken == 1); call temp := vinToCels(tempIn);< assume !(chainBroken == 1); assume !(tempIn < 0);assume true; celsius := kelvin - 273;assume !(chainBroken == 1); assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume temp > 8;assume !(chainBroken == 1); 

	terminating [ ] | nonterminating [+] | correct [4501ms] |  With Error 1 & 2
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 2";
	
		Stem: init := 0;assume true; tempDisplay := 0;assume true; warnLED := 1;assume true; tempIn := 0;assume true; error := 0;assume true; chainBroken := 0;assume true; warnLight := 0;assume true; temp := 0;assume true; time := 0;assume true; init := 1;assume true; assume true;assume true; havoc limes;assume true; assume !(limes > 10);assume true; error := 0;assume true; call display(0, error, 1);< assume true; assume onlyWarn != 0;assume true; tempDisplay := tempdiff;assume true; warnLED := warn;assume true; assume true;assume true; >return call display(0, error, 1); assume true; call coolantControl();< assume true; assume true;assume true; time := time + 1;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; error := 0;assume true; celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume temp > 8 && init == 1; assume temp > 8;assume !(chainBroken == 1); 
		Loop: chainBroken := 1;assume true; assume true;assume true; time := time + 1;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; error := 0;assume true; celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume !(temp > 8);assume true; chainBroken := 0;assume !(chainBroken == 1); assume true;assume true; time := time + 1;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume !(chainBroken == 1); error := 0;assume !(chainBroken == 1); celsius := kelvin - 273;assume !(chainBroken == 1); assume true;assume !(chainBroken == 1); >return call temp := vinToCels(tempIn); assume true; assume temp > 8;assume !(chainBroken == 1); 

	terminating [ ] | nonterminating [+] | correct [3905ms] |  With Error 3
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 2";
	
		Stem: init := 0;assume true; tempDisplay := 0;assume true; warnLED := 1;assume true; tempIn := 0;assume true; error := 0;assume true; chainBroken := 0;assume true; warnLight := 0;assume true; temp := 0;assume true; time := 0;assume true; init := 1;assume true; assume true;assume true; havoc limes;assume true; assume !(limes > 10);assume true; error := 0;assume true; call display(0, error, 1);< assume true; assume onlyWarn != 0;assume true; tempDisplay := tempdiff;assume true; warnLED := warn;assume true; assume true;assume true; >return call display(0, error, 1); assume true; init := 2;assume true; call coolantControl();< assume true; assume true;assume true; time := time + 1;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; chainBroken := 0;assume true; celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume temp > 8;assume temp > 8 && init == 2; 
		Loop: chainBroken := 1;assume true; assume true;assume true; time := time + 1;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; chainBroken := 0;assume !(chainBroken == 1); celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume temp > 8;assume !(chainBroken == 1); 

		
	
*/

var error, init :int;                                         //boolean values
var tempIn: int;                                              //in parameters
var chainBroken, warnLight, tempDisplay, warnLED: int;        //out parameters
var temp, time: int;                                          //locals

procedure ULTIMATE.start() returns()//initialization
modifies error, tempIn, init, chainBroken, warnLight, temp,tempDisplay, warnLED, time;
{ var limes: int;
  
  init:= 0;
  tempDisplay:= 0 ;
  warnLED := 1;
  tempIn := 0;
  error := 0;
  chainBroken := 0;
  warnLight:= 0;
  temp := 0;
  time := 0;
  init:= 1;
  
  while(true){ 									// await input of temperature limes
	  havoc limes;    							//input of limes (shall not be > 10 because so) temperatur that warning shall be shown
	  if(limes > 10){
		error := 1;
		call display(0, error, 1);
	  } else {
		error := 0;
		call display(0, error, 1);
		break;
	  }
  }
  
  init := 2;
  
  call coolantControl();
}

procedure coolantControl() returns()
modifies error, tempIn, chainBroken,temp,tempDisplay, warnLED,time;
{
  while(true)
  {
	time := time + 1;
    havoc tempIn; 							//poll temperature
	call temp := vinToCels(tempIn);
	if(temp > 8){
      chainBroken := 1;
    } /*else {              				//Error 1
	  chainBroken := 0;
	} */
  }
}

procedure vinToCels(kelvin : int) returns(celsius: int)
modifies error,tempDisplay, warnLED,chainBroken;
{
	if(tempIn < 0){
		error := 1;
	}  /*else {      						// Error 2   
		error := 0;
	} */ /*else {              				// Error 3
	  chainBroken := 0;
	} */
	celsius := kelvin - 273;
}

procedure display(tempdiff: int, warn: int, onlyWarn: int)
modifies tempDisplay, warnLED;
{
  if (onlyWarn != 0){
	tempDisplay := tempdiff;
  }
  warnLED := warn;
}