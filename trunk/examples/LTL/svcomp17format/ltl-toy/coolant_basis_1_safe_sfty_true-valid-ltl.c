
#include <stdio.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int error, tempDisplay, warnLED, tempIn, chainBroken,
warnLight, temp, limit, init;


void display(int tempdiff, int warning)
{
	tempDisplay = tempdiff;
	warnLED = warning;
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
	int otime, time = 0;
	while(1)
	{
		otime = time;
		time = otime + 1;
		tempIn = __VERIFIER_nondet_int();
		temp = vinToCels(tempIn);
		if(temp > limit) 
		{
			chainBroken = 1;
		} //else {
		//	chainBroken = 0;
		//}
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
    warnLight = 0;
    temp = 0;
    limit = 8;
    init = 1;
    int try = 0;
	
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
		if (try >= 3) {
			limit = 7;
			break;
		}
		try++;
	}
	
	init = 3;
	coolantControl();	
}