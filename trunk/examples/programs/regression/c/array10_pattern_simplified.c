//#Safe

/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-08
  
  Simplified version of array-patterns/array10_pattern.c (without arrays)
*/

extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array10_pattern.c", 28, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
extern int __VERIFIER_nondet_int() ;
extern short __VERIFIER_nondet_short() ;

signed long long ARR_SIZE ;

int main()
{
	ARR_SIZE = (signed long long)__VERIFIER_nondet_short() ;
	assume_abort_if_not(ARR_SIZE > 0) ;

	int x = 0;
	int count = 0;
  signed long long sum = 0 ;

	for(count=0;count<ARR_SIZE;count++)
	{
		sum = sum + x;
	}

	__VERIFIER_assert(sum <= (ARR_SIZE-1)*(ARR_SIZE+1)) ;
	return 0 ;
}