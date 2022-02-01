/*
 * agroce_locks.c
 *
 *  Created on: 21.07.2012
 *      Author: ermis
 *
 *      Taken from
 *      Paper Title: Explaining Abstract Counterexamples
 *      Authors: Sagar Chaki · Alex Groce · Ofer Strichman
 */

void process() {
	int x, y, z;
	int lock;
	z = 0;
	lock = 1;
	if (x == 0) {
		if (y == 0)
			z = 1;
	}
	if (y != 0) {
		z = y;
	}
	if (x != 0) {
		z = 2;
		lock = 0;
	} else if (z > 0) {
		z = 3;
		lock = 0;
	}
	//@ assert lock == 0;
}
