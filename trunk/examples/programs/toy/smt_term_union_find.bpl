//#Safe
// UNION FIND: {[Main_g_-1, Main_h_-1, Main_e_7]=Main_g_-1, [Main_b_0, Main_a_-1, Main_c_3]=Main_b_0}

procedure Main() returns () {
  var a, b, c, d, e, f, g, h, i: int;
  assume(a >= 0);
  b := a+2;
  assert(b >= a);
  assert(b != a);
  assert(b > a);
  c := b-2;
  assert(c <= b);
  assert(c < b);
  assert(c != b);
  assert(c == a);
  assume(g >= 0 && h >= 0);
  e := g + h;
  assert(e >= g);
  assert(e >= h);
  assume(i >= 0);
  assert(i >= 0);
}
