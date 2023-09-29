int main(){
  int* p = malloc(sizeof(int));
  *p = 1;
  while (*p > 0) {
    p[0] = 2;
  }
  reach_error();
}
