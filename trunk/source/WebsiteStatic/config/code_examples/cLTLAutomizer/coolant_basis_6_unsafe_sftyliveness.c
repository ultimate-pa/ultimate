//#Unsafe
//@ ltl invariant positive: []( (AP(limit > -273) || AP(limit < 10)) ==> (AP(tempIn < 0) ==> <> AP(warnLED == 1)) );

#include <stdio.h>  

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int error, tempDisplay, warnLED = 0, tempIn = 0, chainBroken,
 temp, otime = 0, time = 0, limit = 0, init = 0;


void display(int tempdiff, int warning)
{
	tempDisplay = tempdiff;
	warnLED = 0;
}

int vinToCels(int kelvin)
{
	if (temp < 0) 
	{
		error = 1;
		display(kelvin - 273, error);
	}
	return kelvin -273;
}

void coolantControl()
{
	while(1)
	{
		otime = time;
		time = otime +1;
		tempIn = __VERIFIER_nondet_int();
		temp = vinToCels(tempIn);
		if(temp > limit) 
		{
			chainBroken = 1;
		}
	}
}

int main()
{
    init = 0;
    tempDisplay = 0;
    warnLED = 1;
    tempIn = 0;
    error = 0;
    chainBroken = 0;
    temp = 0;
    limit = 8;
    init = 1;
	
	while(1)
	{
		int limit = __VERIFIER_nondet_int();
		if(limit < 10 && limit > -273)
		{
			error = 0;
			display(0, error);
			break;
		} else {
			error = 1;
			display(0, error);
		}	
	}
	
	init = 3;
	coolantControl();	
}