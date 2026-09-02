int x = 0;

//@ interrupt service routine GPIO;
void gpio()
{
 x = 1;
}

//@ interrupt masking enable GPIO;
void enable_gpio()
{
 x = 0;
}

int main()
{
 enable_gpio();
 //@ assert(x == 0 || x == 1);
 return 0;
}
