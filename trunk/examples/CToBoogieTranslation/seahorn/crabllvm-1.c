extern int nd (void);

int x = 5;
int y = 3;

int a[10];

int main ()
{
  int i;
  int *p =&x;
  *p= *p + 1;
  for (i=0;i<10;i++)
  {
    if (nd ())
      a[i] =y;
    else 
      a[i] =x;
  }
  y++;
  int res = a[i-1];

  //@assert res >= 0 && res <= 6;
  return res;
}
