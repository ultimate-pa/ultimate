//#Safe
/*-----------------------------------------------------------------------------
 * Interrupt-Driven Program (IDP) for testing ACSL interrupt comment parsing
 * and transformation into a Thread-Based Program (TBP)
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 02.09.2026
 *---------------------------------------------------------------------------*/

typedef enum event {
    EV_NONE,
    EV_GPIO,
    EV_ADC
} event_t;

event_t ev = EV_NONE;

//@ interrupt service routine GPIO;
void gpio()
{
    ev = EV_GPIO;
}

//@ interrupt service routine ADC;
void adc()
{
    ev = EV_ADC;
}

//@ interrupt masking enable GPIO;
void enable_gpio();

//@ interrupt masking enable ADC;
void enable_adc();

//@ interrupt masking disable GPIO;
void disable_gpio();

//@ interrupt masking disable ADC;
void disable_adc();

int main()
{
    //@ assert(ev == EV_NONE);
    enable_gpio();
    //@ assert(ev == EV_NONE || ev == EV_GPIO);
    enable_adc();
    //@ assert(ev == EV_NONE || ev == EV_GPIO || ev == EV_ADC);
    disable_gpio();
    //@ assert(ev == EV_NONE || ev == EV_GPIO || ev == EV_ADC);
    disable_adc();
    //@ assert(ev == EV_NONE || ev == EV_GPIO || ev == EV_ADC);

    return 0;
}
