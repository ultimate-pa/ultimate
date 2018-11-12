/*
	__VERIFIER_nondet_<type>() 
	  Returns a non-deterministic value conforming to <type>
	
	__VERIFIER_assume(_Bool b)
	  Assume that b has to be true after this call. 
	  All program executions for which b is false at this point are treated as non-existent. 
	
	__VERIFIER_error()
	  Reachability of this function call is treated as an error. 
	  After reaching this function call, the program terminates immediatly. 
*/

#define bool _Bool

void main(){

	char x 	= __VERIFIER_nondet_char();
	__VERIFIER_assume(x > 0);
	if(x == 0){
		//this location is unreachable 
		__VERIFIER_error();		
	}
	
	bool a 						= __VERIFIER_nondet__Bool();
	bool b 						= __VERIFIER_nondet_bool();
	float c 					= __VERIFIER_nondet_float();
	double d 					= __VERIFIER_nondet_double();
	int e 						= __VERIFIER_nondet_size_t();
	int f 						= __VERIFIER_nondet_int();
	long g 						= __VERIFIER_nondet_loff_t();
	long h 						= __VERIFIER_nondet_long();
	short i						= __VERIFIER_nondet_short();
	char j 						= __VERIFIER_nondet_pchar();
	void* k 					= __VERIFIER_nondet_pointer();
	unsigned char l 			= __VERIFIER_nondet_uchar();
	unsigned int m 				= __VERIFIER_nondet_unsigned();
	unsigned int n 				= __VERIFIER_nondet_uint();
	unsigned long o 			= __VERIFIER_nondet_ulong();
	unsigned short p 			= __VERIFIER_nondet_ushort();
	char q 						= __VERIFIER_nondet_char();
	
	__VERIFIER_error();		
}
