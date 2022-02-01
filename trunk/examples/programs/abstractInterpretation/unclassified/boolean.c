//#Unsafe

int main() {

	_Bool a = 1;
	_Bool b = 0;

	int i = 0;

	if (a) {
		i++;
	}

	if (b) {
		i--;
	}
	
	//@assert ( a == b );
	return 0;
}
