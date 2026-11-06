procedure PiEuler2() returns (pi: real)
{
  var index: int;
  var indexFloat: real;
  var erreur: real;

  pi := 0.0;
  index := 1;
  indexFloat := 1.0;
  erreur := 1.0;

  while (erreur >= 0.00000008)
  {
    assert indexFloat >= 1.0;
    erreur := 1.0 / indexFloat / indexFloat;
    pi := pi + erreur;
    index := index + 1;
    indexFloat := indexFloat + 1.0;
  }
}
