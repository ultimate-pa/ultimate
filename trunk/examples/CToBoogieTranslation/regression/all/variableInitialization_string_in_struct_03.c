int main() {
  struct stu {
    int i;
    char str[40];
  } s = { 3,  "blabla" };
  &s;
}
