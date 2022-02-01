//#Unsafe
/*
 * According to our algorithm none of the assignments is responsible 
 * for the error.
 * 
 * In contrast to the RelationalDisjunctionAssignment.bpl example
 * bot disjuncts are "not related".
 * 
 * WP sequence     false           false        x!=5/\y!=7
 * trace                     x:=5         y:=7              assume(x==5||y==7);  
 * PRE sequence    true            true         x==5\/y==7
 * SP sequence     true            x==5         x==5/\y==7
 * 
 *   
 * This example also demonstrates several things
 * 
 * 1. We need the intersection of PRE and SP on the left-hand side
 * of our Hoare triple checks, otherwise the assignment y:=7 will
 * be marked _responsible_.
 * 
 * 2. If we take the intersection of PRE and SP on the left-hand side
 * of our Hoare triple checks, unsat cores might not be sufficient
 * to determine responsibility.
 * For the checking responsibility of the assignment y:=7, we check the 
 * Hoare triple
 *     { x==5 }    y:=7    { x!=5/\y!=7 }
 * The statement y:=7 is not needed to show validity of the Hoare triple.
 * However, in a formula-based/satisfiability-based infeasibility proof 
 * there are two reasons for unsatisfiability and our SMT solver might
 * choose the unsat core that is related to y:=7.
 * This is a serious problem in our implementation since we always
 * assert that formula related to the statement y:=7 first and hence
 * the SMT solver will typically choose the for our application 
 * inappropriate unsat core.
 * 
 * Author: Christian Schilling, Matthias Heizmann, Numair Mansur
 * Date: 2017-06-12
 * 
 * 
 */

procedure main() returns () {
  var x, y : int;
  x := 5;    // not responsible
  y := 7;    // not responsible
  assume(x == 5 || y == 7);
  assert(false);
}


