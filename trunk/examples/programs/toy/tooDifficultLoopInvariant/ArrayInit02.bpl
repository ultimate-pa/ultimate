//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-09-01
 * 
 * The procedure ULTIMATE.start was obtained by applying a program 
 * transformation to the procedure main.
 * Both procedures are correct.
 */

procedure ULTIMATE.start() 
{
	var i,j,n : int;
// 	var a : [int]int;
	var genericIndex1ForA : int;
	var genericCell1ForA : int;
	var readAuxVar : int;

	i := 0;
	while (i<n) {
		if (i == genericIndex1ForA) {
			genericCell1ForA := 23;
		}
		i := i + 1;
	}
	j :=0;
	while (j<n) {
		havoc readAuxVar;
		if (j == genericIndex1ForA) {
			readAuxVar := genericCell1ForA;
		}
		if (readAuxVar != 23) {
			assume genericIndex1ForA == j;
			assert false;
		}
		j := j + 1;
	}
}



procedure main() 
{
	var i,j,n : int;
	var a : [int]int;

	i := 0;
	while (i<n) {
		a[i] := 23;
		i := i + 1;
	}
	j :=0;
	while (j<n) {
		if (a[j] != 23) {
			assert false;
		}
		j := j + 1;
	}
}

