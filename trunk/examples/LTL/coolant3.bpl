/*
Example properties:

	terminating [+] | nonterminating [ ] | correct [2002ms] | Crashing becuase of java.lang.AssertionError: Bug in run reconstruction of new emptiness test.
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 1";
	
	terminating [ ] | nonterminating [+] | correct [1462ms] | With Error 1
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 1";
		
		Stem: init := 0;assume true; tempIn := 0;assume true; error := 0;assume true; chainBroken := 0;assume true; warnLight := 0;assume true; temp := 0;assume true; init := 1;assume true; call coolantControl();< assume true; assume true;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume temp > 8 && init == 1; assume temp > 8;assume !(chainBroken == 1); 
		Loop: chainBroken := 1;assume true; assume true;assume true; havoc tempIn;assume true; call temp := vinToCels(tempIn);< assume true; assume !(tempIn < 0);assume true; celsius := kelvin - 273;assume true; assume true;assume true; >return call temp := vinToCels(tempIn); assume true; assume !(temp > 8);assume true; chainBroken := 0;assume true; assume true;assume true; havoc tempIn;assume !(chainBroken == 1); call temp := vinToCels(tempIn);< assume !(chainBroken == 1); assume !(tempIn < 0);assume !(chainBroken == 1); celsius := kelvin - 273;assume !(chainBroken == 1); assume true;assume true; >return call temp := vinToCels(tempIn); assume !(chainBroken == 1); assume temp > 8;assume !(chainBroken == 1); 

	terminating [ ] | nonterminating [+] | correct [1692ms] | With Error 1 & 2
		String fileContent = "[](i -> (b -> <>[]a))\n"
		+ "b: temp > 8 \n"
		+ "a: chainBroken = 1\n"
		+ "i: init = 1";	
		
	terminating [+] | nonterminating [ ] | correct [1792ms]
		String fileContent = "[](i -> (!b -> <>[]a))\n"
		+ "b: tempIn >= 0 \n"
		+ "a: error = 1\n"
		+ "i: init = 1";
		
	terminating [ ] | nonterminating [ ] | correct [java.lang.OutOfMemoryError: Java heap space] | With Error  2 
		String fileContent = "[](i -> (!b -> <>[]a))\n"
		+ "b: tempIn >= 0 \n"
		+ "a: error = 1\n"
		+ "i: init = 1";
*/


var error: int;
var tempIn:int;
var init: int;
var chainBroken: int;
var warnLight: int;
var temp: int;

procedure ULTIMATE.start() returns()//initialization
modifies error, tempIn, init, chainBroken, warnLight, temp;
{ init:= 0;
  tempIn := 0;
  error := 0;
  chainBroken := 0;
  warnLight:= 0;
  temp := 0;
  init:= 1;
  call coolantControl();
}

procedure coolantControl() returns()
modifies error, tempIn, chainBroken,temp;
{
  while(true)
  {
    havoc tempIn;  //poll temperaturesensor
	call temp := vinToCels(tempIn);
	if(temp > 8){
      chainBroken := 1;
    }  else {              //Error 1
	  chainBroken := 0;
	}
  }
}

procedure vinToCels(kelvin : int) returns(celsius: int)
modifies error;
{
	if(tempIn < 0){
		error := 1;
	}   else {      // Error: 2   
		error := 0;
	}
	celsius := kelvin - 273;
}