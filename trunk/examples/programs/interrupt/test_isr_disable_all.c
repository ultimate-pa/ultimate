int x = 0;

//@ interrupt service routine GPIO;
void gpio()
{
 x = 1;
}

//@ interrupt service routine ADC0;
void adc0()
{
 x = 2;
}

//@ interrupt masking disable \all;
void disable_all();

int main()
{
 disable_all();
 //@ assert(x == 0 || x == 1 || x == 2);
 return 0;
}
