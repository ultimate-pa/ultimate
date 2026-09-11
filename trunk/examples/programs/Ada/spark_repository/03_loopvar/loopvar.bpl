procedure Loopvar() {
    var x: int;
    var x_old: int;
    var is_first: bool;
    x := 1;
  
    is_first := true;
  
    while (x < 10) {
        if (!is_first) {
          assert x > x_old;
        }
        
        x_old := x;
        is_first := false;
        x := x + 1;
        assert x > 0;
      }
}