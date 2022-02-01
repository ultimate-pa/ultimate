/* 
 * date : 14.7.2015
 * regression test for a bugfix in DetermineNecessaryDeclarations: before it could not
 * determine that e_tag is a necessary declaration because a is referenced in main.
 */

enum e_tag {
	a, b, c, d = 20, e, f, g = 20, h
} var;

int main() {
	//enum e_tag sdf = a; //..would fix the problem we had
	if (a == 0) {
		//@ assert \false;
	}
}
