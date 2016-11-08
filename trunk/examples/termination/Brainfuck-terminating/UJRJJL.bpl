//#Terminating
/*
 * Translated from the Brainfuck program
 * "+[>[[<"
 */

procedure main() returns ()
{
	var head : int;
	var max_head : int;
	var mem : [int] int;
	
	head := 0;
	max_head := 0;
	mem[0] := 0;
	
	mem[head] := mem[head] + 1;
	while (mem[head] != 0) {
		head := head + 1;
		if (head > max_head) {
			mem[head] := 0;
			max_head := max_head + 1;
		}
		while (mem[head] != 0) {
			while (mem[head] != 0) {
				head := head - 1;
				if (head < 0) {
					head := 0;
				}
			}
		}
	}
}
