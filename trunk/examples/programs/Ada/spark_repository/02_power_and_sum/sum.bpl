// sum.bpl
// Model of testsuite/gnatprove/tests/O512-022__power_and_sum/power_and_sum.adb, procedure Sum

procedure Sum(N: int) returns (Result: int)
  requires N >= 1;
  ensures 2 * Result == N * (N + 1);
{
  var I, TotalSum: int;

  I := 1;
  TotalSum := 0;

  while (I <= N)
  {
    TotalSum := TotalSum + I;
    I := I + 1;
  }

  assert 2 * TotalSum == N * (N + 1);
  Result := TotalSum;
}
