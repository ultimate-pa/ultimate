// #Unsafe
// author: Numair Mansur(mansurm@informatik.uni-freiburg.de)
// Simple Call and Return example.

int globalArray[10];

void writeToArray(int value, int location){
	globalArray[location] = value;
}

void main(void) {
	writeToArray(0,11);
}
