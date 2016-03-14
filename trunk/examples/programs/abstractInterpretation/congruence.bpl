procedure main()
{
   var x, y: int;
   
   assume x % 3 == 0;
   assume y % 2 == 0;

   assume x % y == 0;
}