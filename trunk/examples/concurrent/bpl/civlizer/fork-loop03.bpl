var c, i : int;

procedure ULTIMATE.start()
modifies c, i;
{
  c := 0;
  i := 0;

  while (true)
  {
    fork i thread();
    if (i > 0)
    {
      join (i-1);
    }
    i := i + 1;
  }
}

procedure thread()
modifies c;
{
  c := c + i;
  assert c <= 2 * i;
  c := c - i;
}

