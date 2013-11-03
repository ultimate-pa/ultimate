/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * typedef hides inner struct for sizeof.
 */
typedef struct str {
    int i;
} *typeD;

int main() {
  int j = sizeof(struct str);

  return 0;
}
