//#Safe
// doesn't work
/**
 * Loop iterationen in threads müssen um 1 verschoben sein für einfachere Invariante.
 * error for gpp psl It 11, lls It 12
**/

var d : int;
var N, M : int;
var c : int;

procedure ULTIMATE.start()
modifies c, d;
{

  var x1, x2 : int;
  assume N > 1;
  d := 3;
  c := 0;
  fork 1 rec_comp();
  fork 2,2 expl_comp();

  join 1 assign x1;
  join 2,2 assign x2;
  assert (M == N + 1) ==> ((x1 == x2) && ((c == M) || (c == N)));
}

procedure rec_comp()
returns (rec : int)
modifies c;
{
  var i : int;
 
  rec := 0;
  i := 1;

  while (i < N) {
    rec := rec + d;
	i := i+1;
	c := i;
  }
}

procedure expl_comp()
returns (expl : int)
modifies c;
{
  var i : int;
 
  expl := 0;
  i := 1;

  while (i < M) {
    expl :=  (i - 1) * d;
	i := i+1;
	c := i;
  }
}