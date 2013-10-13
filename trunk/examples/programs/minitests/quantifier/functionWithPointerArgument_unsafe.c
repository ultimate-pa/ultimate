int main() {
	int v; 
	int* addrV;
	int w;

	w = add(v, &v);

	if (! (w == 3 * v)) {//bug
		//@assert \false;
		goto ERROR;
	}
	return 0;
}

int add(int x, int* y) {
	return x + *y;
}
