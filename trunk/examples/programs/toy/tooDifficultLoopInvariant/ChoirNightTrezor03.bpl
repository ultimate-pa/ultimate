//#Safe
/*
 * Program obtained from Jochen,
 * related to some Trezor code.
 * 
 * 
 * Date: 2019-06-29
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 */
var a, b, c, i : int;

procedure ULTIMATE.start()
  modifies a,b,c,i;
{

  if (a > 1000000) {
    return;
  }

  b := 0;
  i := 0;
  while(i < a) {
	  if (*) {
		  b := b + 1;
	  }
	  i := i + 1;
  }
  
  c := a - b;
  if (c < 1) {
	  return;
  }

  assert b < a;

}

