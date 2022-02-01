procedure ~init () {

}

procedure bla ()
{
   var x : int;
   var y : int;
   x := 0;
   y := 0;
   while (*) {
       x := x + 1;
       y := y + 1;
   }
   assert x == y; 
}
