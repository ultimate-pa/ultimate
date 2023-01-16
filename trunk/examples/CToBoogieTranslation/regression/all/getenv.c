//#Unsafe

extern char *( __attribute__((__warn_unused_result__, __nonnull__(1))) getenv)(char const   *__name )  __attribute__((__nothrow__)) ;

int main() {
  char* myvar = getenv("MYVAR");
  if (myvar != (char*)0) {
    char x = myvar[0];
    //@ assert x == 97;
  }
}
