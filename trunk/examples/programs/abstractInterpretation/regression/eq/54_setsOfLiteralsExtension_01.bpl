//#Safe
/*
 * The VPDomain should be able to solve this once support for constraints of
 * the form "e in L" is added, where L is a set of literals.
 *  working title for these constraints: "containment predicates"
 */
procedure main() {
  var x : int;

  // side note: making "5" a tracked literal like in the below statement
  // would allow proving at least the second assertion below already in the
  // state of VPDomain without the containment predicates (because the join
  //  preserves known disequalities already and all known literals are pairwise
  //  unequal.)
  // x := 5;

  // taking four branches to make sure this is not solved by disjuctive 
  // completion (whose current default degree in Ultimate is 2 I think)
  //  with a disjunction completion of degree 4 the assertions can be proved
  //  without containment predicates.
  if (*) {
    x := 1;
  } else if (*) {
    x := 2;
  } else if (*) {
    x := 3;
  } else {
    x := 4;
  }
  assert x == 1 || x == 2 || x == 3 || x == 4;
  assert x != 5;
}
