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

//@ interrupt masking enable GPIO;
void enable_gpio();

//@ interrupt masking enable ADC0;
void enable_adc0();

int main()
{
 enable_gpio();
 enable_adc0();
 //@ assert(x == 0 || x == 1 || x == 2);
 return 0;
}
