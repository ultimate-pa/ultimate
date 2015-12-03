int x;

/*@ requires \true;
  @ ensures x > 101 || \result == 91;
  @*/
int f91(int x);

int f91(int x) {
	if (x > 100)
		return x -10;
	else {
		return f91(f91(x+11));
	}
}
