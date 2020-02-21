//#Unsafe
/*-----------------------------------------------------------------------------
 * thad_if-else_bug.c - program to demonstrate bug in ACSL-to-Boogie translator
 *-----------------------------------------------------------------------------
 * author: Manuel Bentele
 * date  : Jan 30, 2020
 * copyright (c) Manuel Bentele
 *-----------------------------------------------------------------------------
  
  2020-02-21: Minified by Daniel Dietsch, 
  Description:
  Translation to Boogie skips assertion in else if branch if if-branch has two asserts 
  Root cause: 
  Bug in CHandler.checkForACSL() did try to advance ACSL next iterator for each ACSL statement in one scope, effectively skipping later ACSL nodes .

 */
void main(void) {
    int request = 2;
    if (request == 1) {
        /*@ assert \false; */
        /*@ assert \false; */
    } else if (request == 2) {
        /*@ assert \false; */
    }
}
