//#Unknown
/*
 * DD 2016-10-11
 * The builtin function __builtin_return_address() should be supported
 * 
 * it should set the overapproximation flag
 */
int main() 
{ 
 for (int i = 0; i < 4; i++) {
  void *tmp ;
  tmp = __builtin_return_address(0);

 }
  //@ assert \false;
}
