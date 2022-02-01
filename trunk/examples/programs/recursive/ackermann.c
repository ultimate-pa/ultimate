//#Safe
/*
 * The ackermann function.
 * Implementation the version defined by Rózsa Péter.
 * http://en.wikipedia.org/wiki/ackermann_function
 * The program is correct with respect to the ensures statement.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2.8.2010
 * 
 */

/*@ requires m >= 0;
  @ requires n >= 0;
  @ ensures \result >= 0;
  @*/
int ackermann(int m, int n);

int ackermann(int m, int n) {
    if (m==0) {
        return n+1;
    }
    if (n==0) {
        return ackermann(m-1,1);
    }
    return ackermann(m-1,ackermann(m,n-1));
}


