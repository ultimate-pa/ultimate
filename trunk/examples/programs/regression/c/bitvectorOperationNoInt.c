// #Safe
/*
 * Date: November 2013
 * Author: Christian Schilling, Matthias Heizmann
 * 
 * bitvector operation with non-integer operands
 */
int main() {
    int i = 500;
    i = i & ((unsigned char)255);
    //@ assert i == 0;
    
    return 0;
}
