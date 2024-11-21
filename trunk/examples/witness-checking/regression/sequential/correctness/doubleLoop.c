void main()
{
  int x = 0;
  int y = 0;
  int i;
  for (i=0; i<=2; i++) {
    x += i;
  }
  for (i=0; i<=2; i++) {
    y += i;
  }
  if (x != y) {
    reach_error();
  }
}

