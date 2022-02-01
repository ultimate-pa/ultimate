//#Safe
/* Variant of AddressOfVariable01-Safe.c were we additionally require that
 * the variable x and a store the same values.
 * 
 * fails in r11749 with the following error
 * java.lang.RuntimeException: There was an error during the translation process! [class java.lang.UnsupportedOperationException, HeapLValues must be converted to RValue before their value can be queried.]
 *
 * 
 * Date: June 2014
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

int nonMain() {
	int x;
	int *p = &x;
	int a = *p;
	//@ assert a == x;
}
