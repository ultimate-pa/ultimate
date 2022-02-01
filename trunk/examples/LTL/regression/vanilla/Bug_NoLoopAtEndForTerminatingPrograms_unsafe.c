//#Unsafe
//Bug: There is no "assume true" loop at final locations of the program, therefore terminating traces are always safe

//@ ltl invariant inv: <>AP(output == 1);

int counter;
int output;

int main() {
  output = 0;
  counter = 1;

  while(counter > 0) {
	  counter--;
  }
}

