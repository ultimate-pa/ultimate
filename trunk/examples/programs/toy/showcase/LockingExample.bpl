//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * The "Locking Example" which occurs in e.g.
 *
 * Thomas A. Henzinger, Ranjit Jhala, Rupak Majumdar, Grégoire Sutre: Lazy abstraction. POPL 2002
 * Kenneth L. McMillan: Lazy Abstraction with Interpolants. CAV 2006
 *
 * We modified the example slightly: The procedures lock and unlock are modelled
 * by the assignment L:=1 and L:=0.
 *
 * The program is correct with respect to the assertions. 
 */

procedure lockingEx()
{
  var L, new, auld: int;

  L := 0;

  while (true) {
    assert(L != 1);
    L := 1;
    auld := new;
    if (*) {
      L :=0;
      new := new + 1;
    }
    if (new == auld) {
      break;
    }
  } 
}

