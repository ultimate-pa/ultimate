void main() {
  int i = 0;
  LOOP:
    if (i < 5) {
      i++;
      goto LOOP;
    }
  if (i != 5) reach_error();
}