//#Unsafe
/*
 * 
 * Date: 2017-10-24
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

int main() {
    int i = 0;
    while(i <= 987654321) {
        i++;
    }
    if (i >= 5) {
        //@ assert \false;
    }
    return 0;
}

