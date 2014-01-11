//#Safe
/*
 * Example taken from a draft titled
 * "Using Program-specific Summaries in Deductive Verification" 
 * written by 
 * Marius Greitschus, Sergio Feo-Arenis, Bernd Westphal, Daniel Dietsch, 
 * and Andreas Podelski
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 27.05.2013
 */
int x;
 
void f(int b, int a) {
    if (b) {
        x = 2*a;
    } else {
        x = 2*a+1;
    }
}

/*@ requires (y>=0 && y<=100);
  @
  @*/
int main(int y);


int main(int y) {
    int b;
    if (y % 2) {
        b = 1;
    } else {
        b = 0;
    }
    f(b,y);
    //@ assert ((y % 2 ==0) ==> (x % 2) != 0 );
}