procedure main()
{
   var x, y, z : int;
   var b : bool;
   
   assume x == y <==> z == 5;
   assume x == y ==>  z == 5;
   assume !(x == y <==> z == 5);
   assume !(x == y ==>  z == 5);

   //assume y % 4 == 0;
   //assume x % 3 == y;
   
   //assume !((x + 2) * (3 + 7) + (14 % -5) * (8 / 7) * y == 0 && y == 7);
}