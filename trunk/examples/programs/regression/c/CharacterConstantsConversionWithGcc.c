//#Safe
/* 
 * According to C11 6.4.4.4.9 the type of character constants is unsigned char.
 * Conversion from unsigned char to signed char is implementation defined 
 * in C11.
 * GCC on amd64 systems converts 255 to -1.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-03-04
 * 
 */

int main(void) {
    char cSomeHexEscSeq = '\xFF';
    if (cSomeHexEscSeq != -1) {
        //@ assert \false;
    }    
    return 0;
}
