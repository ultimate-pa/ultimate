//#Safe
/* Date: 2017-03-24
 * Author: denniswoelfing@gmx.de
 *
 * A loop that where we can calculate an accelerated Icfg but where we cannot
 * eliminate quantifiers. To proof correctnes of this program the Automizer
 * option "Use seperate solver for trace checks" needs to be disabled because
 * SMTInterpol does not like quantifiers.
 */

procedure main() {
	var x : int;
	x := 0;
	while (x < 1000000) {
		x := x + 2;
	}
	assert x == 1000000;
}
