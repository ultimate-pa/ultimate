//#Safe
/* Date: 2017-04-15
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x : int;
	x := 0;
loop:
	if (x >= 1000000) {
		goto end;
	}
	x := x + 1;
	goto loop;
end:
	assert x == 1000000;
}
