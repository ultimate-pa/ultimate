//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

int main() {
	/* bitwise complement */
	{
		int x = 0;
		int y = ~x;
		//@ assert y == -1;
	}
}
