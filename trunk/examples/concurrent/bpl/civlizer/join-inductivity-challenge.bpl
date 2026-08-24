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

   join 2; // <-- inductivity fails if we don't rule out that thread2() may be joined here
   // y == 0
   assert y == 0;

   fork 2 thread2();
}

procedure thread2()
modifies y;
{
    y := 1;
    // ID == 2 && y == 1
}

procedure thread()
modifies y;
{
   y := 0;
   // ID == 1 || (ID == 2 && y == 0)
}

