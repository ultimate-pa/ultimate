/*
 * agroce_minmax.c
 *
 *  Created on: 21.07.2012
 *      Author: ermis
 *
 *      Taken from
 *      Paper Title: Explaining Abstract Counterexamples
 *      Authors: Sagar Chaki · Alex Groce · Ofer Strichman
 */
int main() {
	int input1, input2, input3;
	input1 = 2;
	input2 = 1;
	input3 = 3;
	int least = input1;
	int most = input1;
	if (most < input2)
		most = input2;
	if (most < input3)
		most = input3;
	if (least > input2)
		most = input2; //ERROR!
	if (least > input3)
		least = input3;
	//@ assert least <= most;
}
