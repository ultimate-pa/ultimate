
procedure main()
{
  var v, resi: int;
  var ret0, ret1, ret2, ret3, ret4, resb: bool;

  ret2 := ret2;
  ret4 := ret4;
  ret1 := ret1;
  v := 2;
  ret2 := true;
  ret4 := true;
  ret1 := true;
  havoc ret0;
  havoc resi;
  havoc resb;
  
  
  while (true) {
    ret2 := ret2;
    ret3 := ret3;

    v := 2;
    ret2 := true;
    ret3 := true;
    havoc resb;
  }

}

