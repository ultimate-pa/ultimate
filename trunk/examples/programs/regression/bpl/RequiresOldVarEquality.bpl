//#Safe
/*
 * To prove this program correct, Ultimate needs to consider the implicit precondition that g == old(g).
 * As of 2024-12-18, this precondition was not considered in library mode, and thus Automizer wrongly claimed that this program is incorrect.
 *
 * This is a Boogie version of ../c/RequiresOldVarEquality.c to make sure that the problem is fixed for both C and Boogie programs.
 */

var g : int;

procedure increment()
requires g < 1048;
ensures g > old(g);
modifies g;
{
    g := g + 1;
    while (*)
      invariant (g > old(g));
    {
        g := g + 1;
    }
}
