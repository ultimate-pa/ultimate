/*
Example for 
java.lang.NullPointerException
	at de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes.extractIntegerValueInteger(TypeSizes.java:369)

2018-1015 DD
 */

int main(void){
    unsigned char x = 1;
    unsigned char y = 1;
    
    y = (unsigned char )(~ (1 << (int )x) );
    
    
    return 0;
}