//#rNonTerminationDerivable
/*
 * Date: 2015-09-07
 * Author: Jan Leike, Matthias Heizmann
 * 
 * NonterminationDifficult08 with Integers
 *
 */

procedure main() returns (x, y: int)
{
  while (x + y >= 1 && x + 1 <= 0) {
    x := 2*x;
    y := 3*y;
  }
}

// #\     |#
// ##\    |#
// ###\   |#
// ####\  |#
// #####\ |#
// ######\|#
// #########



// alternative formulation of same problem 
// that might be slightly easier to understand
//
//  while (y >= x + 1 && x >= 1) {
//    x := 2*x;
//    y := 3*y;
//  }
//
//
// #|     /#
// #|    /##
// #|   /###
// #|  /####
// #| /#####
// #|/######
// #########