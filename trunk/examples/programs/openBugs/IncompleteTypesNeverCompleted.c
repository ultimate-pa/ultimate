/* #Safe
 * 
 * For reproducing Issue #377
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2018-10-08
 */


typedef struct myIncompleteStruct myNewName;
extern const myNewName myGlobalVar;

int main(void) {
	return 0;
}
