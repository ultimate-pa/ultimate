// source: originally from http://www.cplusplus.com/reference/cstdio/fprintf/
#include <stdio.h>

int main ()
{
   FILE * pFile;
   int data[1]; 
   data[0] = 42;
   // this will be detected
   // data[-1] = 42;

   pFile = fopen("dummy.txt","w");
   // this will not be detected
   fprintf (pFile, "Answer: %d \n", data[-1]);
   fclose (pFile);
   return 0;
}
