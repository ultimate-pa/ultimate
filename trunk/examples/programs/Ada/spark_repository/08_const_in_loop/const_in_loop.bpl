procedure Const_In_Loop() returns (Z: int)
  ensures Z >= 1;
{
    var V1: int, V2: int;
    var X: int;
    var T_Last: int;

    V1 := 1;
    V2 := 1;
    Z := 1;

    while (true)
    {
        X := Z;
        assert X >= 1;
        T_Last := X;

        if (Z == 1) {
          V1 := T_Last;
        }
        V2 := T_Last;

        assert V1 == V2;

        Z := 2;
    }
}
