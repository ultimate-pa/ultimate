/* #Safe
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-10-11
 */


typedef struct myStruct myNewNameForStruct;

struct myStruct {
	int myFirstField;
	int mySecondField;
};

struct mySecondStruct {
	myNewNameForStruct myField;
};

myNewNameForStruct myArray[1U];


int main(void) {
	return 0;
}
