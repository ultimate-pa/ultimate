typedef struct {
	int num;
	int denom;
} fraction ;

int main() {
	fraction frac; //fraction* @frac;
	fraction frac1;
	fraction* fracP;
	
	//force the struct to be on the heap
	fracP = &frac; //fracP = @frac
	//here we need the structConstructor
	frac1 = frac; //frac1 = *@frac

	return 0;
}

