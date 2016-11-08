/*
 * DD 2016-10-11
 * The builtin function __builtin_return_address() should be supported
 * 
 */
int main() 
{ 
  void *tmp ;
  tmp = __builtin_return_address(0);
}