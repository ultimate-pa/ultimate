void delete(char *x, char *y) {
  *y = 0;
  if (0 < x && x < y) {
    while (*x != 0) {
      *x = 0;
      x++;
	}
  }
}

int main() {
  char *x;
  char *y;
  delete(x, y);
  return 0;
}
