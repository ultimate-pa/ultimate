procedure main()
{
   var x, y: int;
   
   assume x % 3 == 0;
   assume y % 2 == 0;
   assume y >= 5;
   
   assert true;
   
   //assume x % y == 0;
   assume x % 2 == y;
}