//#Safe
/* Date: 2018-05-25
 * Author: jonaswerner95@gmail.com
 *
 * A simple program
 *
 */

procedure main() {
	var x,y : int;
	x := 0;
	y := 2;
	
  while (x < 99) {
    if (y % 2 == 0) {
      x := x + 2;
    } else {
      x:=x + 1;
    }
  }	
	assert ((x % 2) == (y % 2));
}
