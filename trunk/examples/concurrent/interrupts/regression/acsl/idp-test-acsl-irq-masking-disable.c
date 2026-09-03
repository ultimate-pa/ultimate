// #SAFE
/*-----------------------------------------------------------------------------
 * Interrupt-Driven Program (IDP) for testing ACSL interrupt comment parsing
 * and transformation into a Thread-Based Program (TBP)
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 02.09.2026
 *---------------------------------------------------------------------------*/

typedef enum event {
    EV_NONE,
    EV_GPIO
} event_t;

event_t ev = EV_NONE;

//@ interrupt service routine GPIO;
void gpio()
{
    ev = EV_GPIO;
}

//@ interrupt masking disable GPIO;
void disable_gpio();

int main()
{
    //@ assert(ev == EV_NONE);
    disable_gpio();
    //@ assert(ev == EV_NONE);

    return 0;
}
