procedure a() returns ()
{
  call b();
  assert false;
}

procedure b() returns ()
ensures (forall bEnd : bool :: true);
{
  call c();
}


procedure c()
requires (forall cStart : bool :: true);
ensures (forall cEnd : bool :: true);
{
}

