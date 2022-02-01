int add(int x, int* y) {
	return x + *y;
}

int main() {
	int v; 
	int* addrV;
	int w;

	w = add(v, &v);

	if (! (w == 2 * v)) {
		//@assert \false;
	}
	return 0;
}


