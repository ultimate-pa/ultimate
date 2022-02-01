// Boogaloo, EHT Zurich: "boogaloo.exe: out of memory"
// Boogie,   Microsoft:  "more than one declaration of type variable: B"
// Ultimate:             ?

type Barrel A;

procedure f<B>(x : B)
ensures true;
{
  var y : Barrel B;
  call f(y);
} 

