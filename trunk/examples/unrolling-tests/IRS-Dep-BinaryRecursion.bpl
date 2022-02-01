procedure McCarthyRec(x: int) returns (res: int);

implementation McCarthyRec(x: int) returns (res: int)
{
  if (x>100) {
    res := x-10;
  }
  else {
    call res :=  McCarthyRec(x + 11);
    call res := McCarthyRec(res);
  }
}



procedure Main(a: int);

implementation Main(a: int)
{
  var b : int;
  call b := McCarthyRec(a);
}