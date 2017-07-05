//#Unsafe
/*
 * Motivating example in the flow sensitive fault localization paper
 * 
 */

procedure main() returns () {
  var x, y, input : int;
  x := 1;
  y := input - 42;
  if(y < 0){
    x := 0;
  }
  
  assert x != 0;
}
