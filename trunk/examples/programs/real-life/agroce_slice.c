/*
 * agroce_slice.c
 *
 *  Created on: 21.07.2012
 *      Author: ermis
 *
 *      Taken from
 *      Paper Title: Error explanation with distance metrics
 *      Authors: Alex Groce · Sagar Chaki · Daniel Kroening · Ofer Strichman
 */

int main() {
	int input1, input2;
	input1 = 2;
	input2 = 1;
	int x = 1, y = 1, z = 1;
	if (input1 > 0) {
		x += 5;
		y += 6;
		z += 4;
	}
	if (input2 > 0) {
		x += 6;
		y += 5;
		z += 4;
	}
	//@ assert x < 10 || y < 10;
}
