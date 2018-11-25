//#Safe
/* 
 * 
 * Example demonstrates the following problem:
 * 1. When we dispatch the first declaration of g, 
 *    we construct the Boogie declaration of an off-heap variable ~g~0.
 * 2. In the function foo, we use the variable ~g~0.
 * 3. When we dispatch the second declaration of g, 
 *    we remove the Boogie declaration of ~g~0 and declare a new
 *    on-heap variable ~#g~0. 
 *    (Note that this is a slightly different identifier.)
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-11-24
 */


typedef int u_int;

u_int g;

int foo(void) {
	g++;
}

u_int g;



int main(void)
{
  & g;
  return 0;
}
