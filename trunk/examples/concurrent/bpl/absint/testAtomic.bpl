//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 08.07.2022
 */

var x: int;
var y: int;

procedure thread1() returns()
modifies x,y;
{
  atomic {
    havoc x;
    havoc y;
    assume x > y;
  }
}

procedure ULTIMATE.start() returns()
modifies x,y;
{
 y := 1;
 x := 2;
 fork 1 thread1();
 assert x > y;
}
