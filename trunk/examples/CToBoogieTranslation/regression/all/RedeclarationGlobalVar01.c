//#Safe
/* 
 * 
 * Example demonstrates the following problem:
 * 1. When we dispatch the first declaration of g, 
 *    we construct the Boogie declaration of an on-heap variable ~#g~0.
 * 2. In the main function, we use the variable ~#g~0.
 * 3. When we dispatch the second declaration of g, 
 *    we remove the Boogie declaration of ~#g~0 and declare a new
 *    off-heap variable ~g~0. 
 *    (Note that this is a slightly different identifier.)
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-11-11
 */


struct myStruct {
  int member;
};

static struct myStruct const g;

int main(void)
{
  int *p = & g;
  return 0;
}

static struct myStruct const g = {0}; 
