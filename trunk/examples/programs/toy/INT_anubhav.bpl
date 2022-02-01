//#Safe
//author: unknown
//added by nutz
procedure main(){
  
  var i,j,x,y:int;
  
  x := i;
  y := j;
  
  while(x != 0){
    x := x -1;
	y := y -1;
  }
  
  assert(i != j || y == 0);
}
