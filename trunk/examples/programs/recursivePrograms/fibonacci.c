//#Safe
/*
 * Recursive computation of fibonacci numbers.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 6.5.2011
 *
 */
 
/*@ 
  @ ensures \result >= 0;
  @*/
int fibonacci(int n);

int fibonacci(int n) {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibonacci(n-1) + fibonacci(n-2);
    }
}