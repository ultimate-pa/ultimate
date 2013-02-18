
procedure SimpleTrace(a: int) returns (res: int);

implementation SimpleTrace(a: int) returns (res: int)
{
 call res := SimpleTrace(a);
 call res := SimpleTrace(a);
}

procedure Main(a: int);

implementation Main(a: int)
{
  var b : int;
  call b := SimpleTrace(a);
}