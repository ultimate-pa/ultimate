//#Safe
/* Nontrivial program whose correctness can be shown using a monadic loop
 * invariant.
 * E.g., the following loop invariant is sufficient.
 * 0 <= offset <= 4 * 10000  /\  offset % 4 == 0  /\  length = 4 * 10000
 * Note that the second conjunct (divisibility) is indispensable.
 * 
 * Simplified version of verification problem that occurs regularly if we use
 * Ultimate to very C programs.
 * - The variable offset is the "offset" of some int pointer.
 * - The while loop moves a pointer along some memory area.
 * - The assert checks if we are still in some allocated area.
 * - An int takes four byte, hence the pointer is incremented by four.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2015-09-03
 */

procedure main() returns () {
	var offset : int;
	var length : int;
	offset := 0;
	length := 4 * 10000;
	while (offset < length) {
		assert (4 + offset <= length);
		offset := offset + 4;
	}
}