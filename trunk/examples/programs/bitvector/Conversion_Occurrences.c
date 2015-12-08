//#Safe
/* 
 * Author: langt@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * Date: 2015-08-18
 */


void function(unsigned int a) {
  if (!(a >= 200U )) {
    //@ assert \false;
  }
}

int main() {
  
  signed short minusOne = -1;
  
  /* initializer */
  unsigned int a = minusOne;
  if (!(a >= 200U )) {
    //@ assert \false;
  }
  
  /* assignment */
  unsigned int b = 5;
  b = minusOne;
  if (!(b >= 200U )) {
    //@ assert \false;
  }
  
  /* cast */
  if (!( ((unsigned int) minusOne) >= 200U )) {
    //@ assert \false;
  }
  
  /* function application */
  function(minusOne);
  
  /* ususal arithmetic conversions */
  if (!(minusOne + 0U >= 200U )) {
    //@ assert \false;
  }
  
  

}
