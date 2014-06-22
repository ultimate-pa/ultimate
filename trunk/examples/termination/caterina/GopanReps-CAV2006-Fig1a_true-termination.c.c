/*
 * Program from Fig.1a of
 * 2006CAV - Gopan,Reps - Lookahead Widening
 *
 * Date: 2014-06-22
 * Author: Caterina Urban, Matthias Heizmann
 *
 */

int main() {
	int x = 0, y = 0;
	while (1) {
		if (x <= 50) {
			y++;
		} else {
			y--;
		}
		if (y < 0) {
			break;
		}
		x++;
	}
	return 0;
}