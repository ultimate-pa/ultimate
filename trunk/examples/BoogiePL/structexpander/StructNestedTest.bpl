type rational = { n, d: int, v:real };
type complex = { rel, img : rational };

procedure add (a: rational, b: rational) returns (r:rational)
{
   r := { n: a!n*b!d + b!n*a!d, d: a!d*b!d, v: a!v+b!v };
}

procedure addc (a: complex, b:complex) returns (r:complex)
{
   var rel, img : rational;

   call rel := add(a!rel, b!rel);
   call img := add(a!img, b!img);

   r!rel := rel;
   r!img := img;
}
