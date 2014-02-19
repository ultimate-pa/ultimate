procedure nplus(b:int) returns (c:int)
{
  var zwischen: int;
  if(b > 0) {
    call zwischen := nplus(b-1);
  } else { 
    zwischen := 0;
  }
  c := zwischen + b; 
}