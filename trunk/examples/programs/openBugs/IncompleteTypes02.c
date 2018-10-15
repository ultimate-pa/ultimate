/* #Safe
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-10-11
 */

typedef enum myEnum myNewNameForEnum;
typedef struct myStruct myNewNameForStruct;
typedef union myUnion myNewNameForUnion;

struct myPointerStruct {
	myNewNameForEnum *p1;
	myNewNameForStruct *p2;
	myNewNameForUnion *p3;
};

enum myEnum {
	foo,
	bar,
};

struct myStruct {
	int myFirstField;
	myNewNameForEnum mySecondField;
};

union myUnion {
	int myFirstMember;
	myNewNameForStruct mySecondMember ;
};


struct myNonPointerStruct {
	myNewNameForEnum myField1;
	myNewNameForStruct myField2;
	myNewNameForUnion myField3;
};

myNewNameForEnum myEnumArray[1];
myNewNameForStruct myStructArray[1];
myNewNameForUnion myUnionArray[1];


int main(void) {
	myNewNameForEnum e = foo;
	struct myPointerStruct x;
	x.p1 = &e;
	return 0;
}
