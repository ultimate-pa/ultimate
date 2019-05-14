void sub() {
  int j;
  j = 4;
  //@ assert 5 > 0;
  j = 6;
  //@ assert 7 > 0;
}

void main() {
  int i;
  i = 1;
  sub();
  while (i < 2) {
  	i = i + 3;
  }
}

