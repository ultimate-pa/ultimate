/* #Unsafe
 * 
 * Test that we may not expect that local var a has been initialized.
 * TODO: More detailed explantation what kind of variable a is according to
 * C99 standard.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 28.3.2013
 * 
 */

int main() {
    int a;
    //@ assert a == 0;
}
