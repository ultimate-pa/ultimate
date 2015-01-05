procedure f<a>(x:a)
{
  fBodyPlaceholder:
}

procedure g()
{
  call f(5);
  call f(true);
}

procedure u<a>(x:a)
{
  // body f
}

procedure v<b>(x:b)
{
  call u(x);
}

procedure vFlatVersion<b>(x:b)
{
  var v_x : b;
}

