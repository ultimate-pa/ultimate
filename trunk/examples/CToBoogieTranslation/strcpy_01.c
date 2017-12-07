#include<string.h>
#include<stdio.h>
int main() {
  char str1[] = "bla";
  char str2[4];

  strcpy(str2, str1);

  printf("str1: %s\n", str1);
  printf("str2: %s\n", str2);

  printf("str2[1]: %c\n", str2[1]);
  printf("str2[3]: %c\n", str2[3]);

  if (str2[1] != 'l') {
    //@ assert \false;
  }
  if (str2[3] != '\0') {
    //@ assert \false;
  }
}
