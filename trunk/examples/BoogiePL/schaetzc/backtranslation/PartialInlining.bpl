procedure a()
requires (forall aStart : bool :: true);
ensures (forall aEnd : bool :: true);
{
	call b();
  assert false;
}

procedure b()
requires (forall bStart : bool :: true);
ensures (forall bEnd : bool :: true);
{
	call c();
	if (false) {
	  call b();
	}
}

procedure c()
requires (forall cStart : bool :: true);
ensures (forall cEnd : bool :: true);
{
  call d();
}

procedure d()
requires (forall dStart : bool :: true);
ensures (forall dEnd : bool :: true);
{
  assume (forall dMid : bool :: true);
}

