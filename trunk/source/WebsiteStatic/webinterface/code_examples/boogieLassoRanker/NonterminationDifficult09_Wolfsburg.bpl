//#rNonTermination
/*
 * Date: 2015-09-24
 * Author: Matthias Heizmann
 * Program is nonterminating over the integers.
 * However the program does not have a geometric nontermination argument over
 * the integers. (Problem: non-rational eigenvalues)
 * 
 * Can be seen as a simplified version of Hanoi_plus_false-termination.c
 * which Ton Chanh Le submitted to the TermComp 2015.
 */

procedure main() returns (x: int, y: int)
{
  while (x >= 1) {
    x,y := x + y, x;
  }
}

