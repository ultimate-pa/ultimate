/*
Example properties:
	terminating [+] | nonterminating [ ] | correct [2018ms]
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > limit \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 2";

	terminating [ ] | nonterminating [ ] | correct [3194ms] |  With Error 1
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 2";

		Stem: init := 0;assume true; tempDisplay := 0;assume true; warnLED := 1;assume true; tempIn := 0;assume true; error := 0;assume true; chainBroken := 0;assume true; warnLight := 0;assume true; temp := 0;assume true; time := 0;assume true; init := 1;assume true; assume true;assume true; havoc limit;assume true; assume !(limit > 10 || limit < -273);assume true; error := 0;assume true; call display(0, error, 1);< assume true; assume onlyWarn != 0;assume true; tempDisplay := tempdiff;assume true; warnLED := warn;assume true; assume true;assume true; >return call display(0, error, 1); assume true; init := 2;assume temp > limit && init == 2; call coolantControl();< assume !(chainBroken == 1); 
		Loop: assume true;assume !(chainBroken == 1); time := time + 1;assume !(chainBroken == 1); havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume !(chainBroken == 1); celsius := kelvin - 273;assume !(chainBroken == 1); assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume !(temp > limit);assume !(chainBroken == 1); chainBroken := 0;assume !(chainBroken == 1); 
		
	terminating [-] | nonterminating [-] | correct [-] | java.lang.OutOfMemoryError: Java heap space
	String fileContent = "<>a\n"
		+ "a: time > 1\n"	
		
	terminating [+] | nonterminating [ ] | correct [1428ms] | Without Codeblock 4
	String fileContent = "<>a\n"
		+ "a: time > 0 \n";	
		
	terminating [+] | nonterminating [ ] | correct [1428ms] | Without +1 an Stelle 5 Without Codeblock 4
	String fileContent = "<>a\n"
		+ "a: time > 0 \n";	
		
		Stem: init := 0;assume !(time > 0); tempDisplay := 0;assume !(time > 0); warnLED := 1;assume !(time > 0); tempIn := 0;assume !(time > 0); error := 0;assume !(time > 0); chainBroken := 0;assume !(time > 0); warnLight := 0;assume !(time > 0); temp := 0;assume !(time > 0); time := 0;assume !(time > 0); limit := 8;assume !(time > 0); init := 1;assume !(time > 0); init := 2;assume !(time > 0); call coolantControl();< assume !(time > 0); 
		Loop: assume true;assume !(time > 0); otime := time;assume !(time > 0); time := otime;assume !(time > 0); havoc tempIn;assume !(time > 0); call temp := vinToCels(tempIn);< assume !(time > 0); assume !(tempIn < 0);assume !(time > 0); celsius := kelvin - 273;assume !(time > 0); assume true;assume !(time > 0); >return call temp := vinToCels(tempIn); assume !(time > 0); assume !(temp > limit);assume !(time > 0); 


	terminating [+] | nonterminating [ ] | correct [1428ms] | Without Codeblock 4
	String fileContent = "[]<>a\n"
		+ "a: time > 0 \n";
		
	terminating [+] | nonterminating [ ] | correct [798ms] | Without Codeblock 4
	String fileContent = "[]<>a\n"
		+ "a: time > otime \n";
		
	terminating [ ] | nonterminating [+] | correct [1428ms] | Without Codeblock 4 with and error 5
	String fileContent = "[]<>a\n"
		+ "a: time > 0 \n";
		
		Stem: init := 0;assume !(time > 0); tempDisplay := 0;assume !(time > 0); warnLED := 1;assume !(time > 0); tempIn := 0;assume !(time > 0); error := 0;assume !(time > 0); chainBroken := 0;assume !(time > 0); warnLight := 0;assume !(time > 0); temp := 0;assume !(time > 0); time := 0;assume !(time > 0); limit := 8;assume !(time > 0); init := 1;assume !(time > 0); init := 2;assume !(time > 0); call coolantControl();< assume !(time > 0); 
		Loop: assume true;assume !(time > 0); otime := time;assume !(time > 0); time := otime;assume !(time > 0); havoc tempIn;assume !(time > 0); call temp := vinToCels(tempIn);< assume !(time > 0); assume !(tempIn < 0);assume !(time > 0); celsius := kelvin - 273;assume !(time > 0); assume true;assume !(time > 0); >return call temp := vinToCels(tempIn); assume !(time > 0); assume !(temp > limit);assume !(time > 0); 

	terminating [ ] | nonterminating [+] | correct [798ms] | Without Codeblock 4 with and error 5
	String fileContent = "[]<>a\n"
		+ "a: time > otime \n";
		
		Stem: init := 0;assume true; tempDisplay := 0;assume !(time > otime); warnLED := 1;assume !(time > otime); tempIn := 0;assume !(time > otime); error := 0;assume !(time > otime); chainBroken := 0;assume !(time > otime); warnLight := 0;assume !(time > otime); temp := 0;assume !(time > otime); time := 0;assume !(time > otime); limit := 8;assume !(time > otime); init := 1;assume !(time > otime); init := 2;assume !(time > otime); call coolantControl();< assume !(time > otime); 
		Loop: assume true;assume !(time > otime); otime := time;assume !(time > otime); time := otime;assume !(time > otime); havoc tempIn;assume !(time > otime); call temp := vinToCels(tempIn);< assume !(time > otime); assume !(tempIn < 0);assume !(time > otime); celsius := kelvin - 273;assume !(time > otime); assume true;assume !(time > otime); >return call temp := vinToCels(tempIn); assume !(time > otime); assume !(temp > limit);assume !(time > otime); 

	terminating [+] | nonterminating [ ] | correct [+] | with marker 6 
	String fileContent = "c U((b U []i) || [] b)\n"
			+ "b: init = 1\n"
			+ "i: init = 2\n"
			+ "c: init = 0"
			
	terminating [ ] | nonterminating [+] | correct [19491ms] | with marker 6 and Error 7
	String fileContent = "c U((b U []i) || [] b)\n"
			+ "b: init = 1\n"
			+ "i: init = 2\n"
			+ "c: init = 0"
			
		Stem: init := 0;assume !(init == 1); tempDisplay := 0;assume !(init == 2); warnLED := 1;assume true; tempIn := 0;assume !(init == 1); error := 0;assume true; chainBroken := 0;assume true; warnLight := 0;assume !(init == 2); temp := 0;assume true; time := 0;assume !(init == 1); limit := 8;assume true; init := 1;assume !(init == 2); assume true;assume !(init == 0); havoc limit;assume true; assume limit > 10;assume true; error := 1;assume true; call display(0, error, 1);< assume true; assume onlyWarn != 0;assume true; tempDisplay := tempdiff;assume true; init := 0;assume !(init == 1); warnLED := warn;assume true; assume true;assume !(init == 2); >return call display(0, error, 1); 
		Loop: assume true; assume true;assume true; havoc limit;assume true; assume limit > 10;assume true; error := 1;assume true; call display(0, error, 1);< assume true; assume onlyWarn != 0;assume true; tempDisplay := tempdiff;assume true; init := 0;assume true; warnLED := warn;assume true; assume true;assume true; >return call display(0, error, 1); 

	terminating [+] | nonterminating [ ] | correct [1492ms] | with marker 6
		String fileContent = "[]( i-> <>a)\n"
			+ "a: time > otime \n"
			+ "i: init = 2 \n";
			
	terminating [ ] | nonterminating [+] | correct [1532ms] | with marker 6 error 5
		String fileContent = "[]( i-> <>a)\n"
			+ "a: time > otime \n"
			+ "i: init = 2 \n";
			
		Stem: init := 0;assume true; tempDisplay := 0;assume true; warnLED := 1;assume true; tempIn := 0;assume true; error := 0;assume true; chainBroken := 0;assume true; warnLight := 0;assume true; temp := 0;assume true; time := 0;assume true; limit := 8;assume true; init := 1;assume true; assume true;assume true; havoc limit;assume true; assume !(limit > 10);assume true; error := 0;assume true; call display(0, error, 1);< assume true; assume onlyWarn != 0;assume true; tempDisplay := tempdiff;assume true; init := 0;assume true; warnLED := warn;assume true; assume true;assume true; >return call display(0, error, 1); assume true; init := 2;assume !(time > otime) && init == 2; call coolantControl();< assume !(time > otime); 
		Loop: assume true;assume !(time > otime); otime := time;assume !(time > otime); time := otime;assume !(time > otime); havoc tempIn;assume !(time > otime); call temp := vinToCels(tempIn);< assume !(time > otime); assume !(tempIn < 0);assume !(time > otime); celsius := kelvin - 273;assume !(time > otime); assume true;assume !(time > otime); >return call temp := vinToCels(tempIn); assume !(time > otime); assume !(temp > limit);assume !(time > otime); 

*/

var error, init :int;                                         //boolean values
var tempIn: int;                                              //in parameters
var chainBroken, warnLight, tempDisplay, warnLED: int;        //out parameters
var temp, time, limit, otime: int;                                          //locals

procedure ULTIMATE.start() returns()//initialization
modifies error, tempIn, init, chainBroken, warnLight, temp,tempDisplay, warnLED, time, limit, otime;
{ 
     init:= 0; tempDisplay:= 0 ; warnLED:= 1; tempIn:= 0;error:= 0;
   chainBroken := 0; warnLight:= 0;temp := 0; time := 0; limit := 8; init:= 1;
  
   while(true){             // await input of temperature limit
      havoc limit;          // input of limit
      if(limit < 10 && limit > -273){
		error := 0;
		call display(0, error);
		break;
	  } else { 
		error := 1;
		call display(0, error);
      }
	 }
	  
  init := 3;   //error 6 ... zuweisung auskommentieren
  call coolantControl();
}

procedure coolantControl() returns()
modifies error, tempIn, chainBroken,temp,tempDisplay, warnLED,time,otime,init;
{
  while(true)
  {
	otime := time;
	time := otime + 1; 						//kein + error 5
    havoc tempIn; 							//poll temperature
	call temp := vinToCels(tempIn);
	if(temp > limit){
      chainBroken := 1;
    } /*else {              				//Error 1
	  chainBroken := 0;
	} */
  }
}

procedure vinToCels(kelvin : int) returns(celsius: int)
modifies error,tempDisplay, warnLED,chainBroken,init;
{
	if(tempIn < 0){
		error := 1;
		call display(kelvin - 273, error);
	}  /*else {      						// Error 2   
		error := 0;
	} */ /* else {              				// Error 3
	  chainBroken := 0;
	} */
	celsius := kelvin - 273;
}

procedure display(tempdiff: int, warn: int)
modifies tempDisplay, warnLED,init;
{
  tempDisplay := tempdiff;
  warnLED := warn;
}