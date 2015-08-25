//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 24.08.2015
 */

int main() {
  char c = 1;

  if (sizeof(char) < sizeof(int)) {
    if (sizeof(+c) != sizeof(int)) {
      //@ assert \false;
    }

    if (sizeof(-c) != sizeof(int)) {
      //@ assert \false;
    }

    if (sizeof(~c) != sizeof(int)) {
      //@ assert \false;
    }
  }
}
