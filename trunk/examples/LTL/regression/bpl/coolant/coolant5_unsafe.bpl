//#Unsafe
//#LTLProperty: AP(init == 0) U((AP(init == 1) U []AP(init == 2)) || [] AP(init == 1))


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