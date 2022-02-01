//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 23.7.2010
 *
 * Implementation of McCarthy's 91 function. The program is correct with
 * respect to assertions.
 * In order to proof correctness one has to infer some requires/ensures pairs
 *
 * The example is taken from our POPL'10 paper "Nested Interpolants".
 *
 * The correctness proof of the orinial McCarthy.bpl is easy, since an assert
 * occurs also as an assume only the base case is "hard" to proof.
 * Therefore this example has a separate Mail procedure.
 */

procedure McCarthy(x: int) returns (res: int);

implementation McCarthy(x: int) returns (res: int)
{
  if (x>100) {
    res := x-10;
  }
  else {
    call res :=  McCarthy(x + 11);
    call res := McCarthy(res);
  }
}


procedure Main(a: int) returns (b: int);
ensures b == 91 || a > 101;
//assert(a<=101 ==> b != 90);

implementation Main(a: int) returns (b: int)
{
  call b := McCarthy(a);
}
