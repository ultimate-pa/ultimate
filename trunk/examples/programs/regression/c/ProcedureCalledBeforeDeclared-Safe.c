/*
 * Date: October 2013
 * Author: Matthias Heizmann
 * 
 */
int main() {
	int i = 0;
	i = inc(i);
	//@ assert i == 1;
	return 0;
}

int inc(int i) {
	return i + 1;
}
