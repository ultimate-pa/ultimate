function ToReal(x: int): real;

function Inv(x: int): real
{
  1.0 / ToReal(x)
}

procedure PiEuler() returns (pi: real)
{
  var index: int;
  var erreur: real;

  pi := 0.0;
  index := 1;
  erreur := 1.0;

  while (erreur >= 0.00000008)
  {
    assert index >= 1;

    erreur := Inv(index);
    pi := pi + erreur;
    index := index + 1;
  }
}
