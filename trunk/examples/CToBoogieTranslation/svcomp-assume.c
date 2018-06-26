//#Safe
// Typing "-" on my machine produces &#45;
// Check your machine's "-" with http://unicodelookup.com/
// "−" (&minus; or 0x2212) vs "-" (&#45; or 0x2D)
// CDT does not recognize "−" (&minus;) as minus, because only "-" (&#45;) is minus
// Note that gcc recognizes this issue! 
void main(){

	char x 	= __VERIFIER_nondet_char();
	__VERIFIER_assume(x > −1);
	if(x == 0){
		__VERIFIER_error();
	}
}
