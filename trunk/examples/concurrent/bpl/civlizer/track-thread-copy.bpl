var y : int;

procedure ULTIMATE.start()
modifies y;
{
    var x : int;
    x := 0;
    while (x < 2) {
        x := x + 1;
        fork x thread();
   }

   join 2;
   assert y == 0;
}

procedure thread()
modifies y;
{
   y := 0;
}

