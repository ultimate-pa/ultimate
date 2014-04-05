//#cSafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 26.1.2010
 *
 * Peterson's algorithm
 */

 var flag0 : int;
 var flag1 : int;
 var turn : int;
 var critical : int;
 
 
procedure ~init() returns();
modifies critical;

implementation ~init()
{
   critical := 0;
}


procedure Thread0() returns ();
modifies critical;
modifies flag0, flag1, turn;
 
implementation Thread0()
{
  var x, y: int;

  while (true) {
    flag0 := 1;
    turn := 1;
    assume (flag1 == 0 || turn == 0);
      assert (critical == 0);
      critical := 1;
      critical := 0;
    flag0 := 0;
  }

}

procedure Thread1() returns ();
modifies critical;
modifies flag0, flag1, turn;

implementation Thread1()
{
   var a, b: int;
 
   while (true) {
     flag1 := 1;
     turn := 0;
     assume (flag0 == 0 || turn == 1);
       assert (critical == 0);
       critical := 1;
       critical := 0;
     flag1 := 0;
   }

}