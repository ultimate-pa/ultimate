//#Unsafe

procedure f() {
	  var i : int;
	  call i := g(i);
	  assert false;
}

procedure g(x : int) returns (y : int);

implementation g(y : int) returns (x : int) {
}
