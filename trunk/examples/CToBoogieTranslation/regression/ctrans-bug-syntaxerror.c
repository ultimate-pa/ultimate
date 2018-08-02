typedef unsigned short __u16;
typedef __u16 __be16;

__inline static __be16 foo()
{
	return 0;
}

int main(void){
	foo();
	return 0;
}

