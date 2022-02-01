int foo(int a, unsigned long b, char c)
{
  return a + (int)(b * c);
}

int main()
{
  return foo(1, 2, 'c');
}
