int x;

/*@ requires x > 0;
  @ ensures y > 5;
  @ ensures \result = 10;
  @*/
int main(int x, int y);

int main(int x, int y) {
	//@ assert x > 0;
	int z = 15;
	//@ assert z == 15;

	while (true) {
		int x = 10;
		//@ assert x == 10;
	}
}

/*@ requires x > 0;
  @
  @*/
int foo();

int foo() { }
