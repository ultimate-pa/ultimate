//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 23.10.2013
 */
type myType;


procedure proc();

implementation proc()
{
  var a: myType;
  var b: myType;
  var c: myType;
  var tmp: myType;
  a := b;
  while (*) {
    tmp := a;
	a := b;
	b := c;
	c := tmp;
	havoc tmp;
  }
  assert a == b || b == c || c == a;
}





  
