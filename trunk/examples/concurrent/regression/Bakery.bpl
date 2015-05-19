//#cSafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 29.1.2010
 *
 * Bakery mutual exclusion algorithm
 */

 var n0 : int;
 var n1 : int;
 var critical : int;
 
 
procedure ~init() returns();
modifies critical;
modifies n0;
modifies n1;

implementation ~init()
{
   critical := 0;
   n0 := 0;
   n1 := 1;
}


procedure Thread0() returns ();
modifies critical;
modifies n0;
 
implementation Thread0()
{
  var x, y: int;

  while (true) {
    n0 := n1+1;
    assume (n1 == 0 || n0<n1);
      assert (critical == 0);
      critical := 1;
      critical := 0;
    n0 := 0;
  }

}

procedure Thread1() returns ();
modifies critical;
modifies n1;

implementation Thread1()
{
   var a, b: int;
 
  while (true) {
    n1 := n0+1;
    assume (n0 == 0 || n1<n0);
      assert (critical == 0);
      critical := 1;
      critical := 0;
    n1 := 0;
  }

}