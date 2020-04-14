//#Safe
/*
 * 2020-04-07
 * Manual example for IsEmptyHeuristic: AssertionError: IsEmptyHeuristic did not match IsEmpty
 * 
 * Author: Bree
 */
 
/* i for outer loop, j for inner loop, both going 0 to n-1 */
void recursion(int n, int i, int j)
{
  if (i < n) {
    if (j < n) {
      // inner loop when j < n
      recursion(n, i, j+1); // increment inner counter only!
    } else { // when j has reached n...
      // outer loop, which restarts inner loop
      recursion(n, i+1, 0); // increment outer counter, reset inner
                            // since we're starting a new inner loop
    }
  }
}

int main(){
    int n,i,j;
    recursion(n,i,j);
}