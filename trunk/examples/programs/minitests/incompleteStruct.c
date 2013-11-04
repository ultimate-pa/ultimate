/*
 * Date: November 2013
 * Author: Christian Schilling and Matthias Heizmann
 * 
 * An incomplete struct definition messes up the complete definition.
 */
struct fraction; /* this line is what causes the error */


struct fraction {
   int num;
   int denom;
};

int main() {
    struct fraction f;
    f.num = 5;
    f.denom = 5;
    //@ assert f.num == f.denom;
    return 0;
}
