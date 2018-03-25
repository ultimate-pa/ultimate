#include "ptrop.h"

int main()
{
  int arr[] = {1, 2, 3};
  int twos = arr[1];
  //@assert twos == 2;
  int two = readInPtrArray(1, arr);
  //@assert two == 2;
  return two;
}
