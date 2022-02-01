//#Unknown
/*
 * DD 2016-10-11
 * The builtin function __builtin_strchr() should be supported
 *
 */
int main()                                                                  
{                                                                               
  char buffer1[40] = "computer program";                                      
  char * ptr;                                                                   
  int    ch = 'p';                                                              

  ptr = __builtin_strchr( buffer1, ch );                                                  
  //printf( "The first occurrence of %c in '%s' is '%s'\n", ch, buffer1, ptr);                                                 
  //@ assert \false;
}  

