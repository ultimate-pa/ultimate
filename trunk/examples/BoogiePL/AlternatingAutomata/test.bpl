procedure ~init () {

}

procedure bla ()
{
   var x : int;
   var y : int;
   var z : int;
   x := 0;
   y := 0;
   z := 0;
   //while (*) {
   //  if (*) {
       x := x + 1;
       // } else if (*) {
       y := y + 1;
    // } else {
       z := z + 1;
     //}
   //}
   assert x + y + z >= 0;
}
