//#Safe
/* Date: 2017-01-25
 * Author: jonaswerner95@gmail.com
 * 
 * Example program for testing
 * loop acceleration using
 * abstract path conditions.
 * 
 */

var k, i, n: int;
var a :[int] int;

procedure main() returns ()
modifies i, k, n;
{
	k := 0;
	i := 3;
	n := 20;
	while (i<n) {
		if (a[i] == 1) {
			k := k + 1;
		}
		i := i + 1;
	}
	if (k > 12) {
		assert(false);
	}
}
