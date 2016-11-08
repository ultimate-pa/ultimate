//#Safe
/*
 * Recursive program which is correct with respect to the assert statement in
 * procedure Main.
 * In order to show correctness we have to show that upDownGlobal does not 
 * change the value of g.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: April 2010
 *
 */

int g;


int upDownGlobal();

int upDownGlobal() {
    g++;
    int nondet;
    if (nondet) {
        upDownGlobal();
    }
    g--;
}


int main();

int main()
{
    int z;
    g = z;
    upDownGlobal();
    //@assert g == z;
}


