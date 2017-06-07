//#Safe
// 2017-06-07: Translation of this example failed due to differences in function declaration location and function implementation location. 

typedef union _ptrUnion {
	volatile const void* p_VOID;
	const float* p_FLOAT;
	const unsigned short int* p_UINT;
	const unsigned char* p_UCHAR;
	const signed short int* p_SINT;
	const signed char* p_SCHAR;
} ptrUnion;

static void myFunc(ptrUnion PtrData);

static void myFunc(ptrUnion PtrData)
{  
  //
}

int main() {
	auto ptrUnion PtrData;
	PtrData.p_VOID = 0;

	myFunc(PtrData);
	
	return 0;
}