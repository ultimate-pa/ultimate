//#Safe
/*-----------------------------------------------------------------------------
 * Interrupt-Driven Program (IDP) for testing IDP verification
 *-----------------------------------------------------------------------------
 * Author: Matthias Zumkeller
 *   Date: 28.04.2026
 *---------------------------------------------------------------------------*/

#include <assert.h>
#include <stdbool.h>

/*-----------------------------------------------------------------------------
 * Macro definitions
 *---------------------------------------------------------------------------*/
#define BTN_PRESSED true
#define BTN_CLEARED false

/*-----------------------------------------------------------------------------
 * Type declarations
 *---------------------------------------------------------------------------*/
typedef enum pin_state {
    PIN_STATE_ON,
    PIN_STATE_OFF
} pin_state_t;

/*-----------------------------------------------------------------------------
 * Global variables
 *---------------------------------------------------------------------------*/
bool button_state = false;
int step_in_isr = false;

/*-----------------------------------------------------------------------------
 * Function declarations
 *---------------------------------------------------------------------------*/
void HAL_GPIO_Init(void);
bool HAL_GPIO_Read(int pin);
void HAL_GPIO_Write(int pin, pin_state_t state);

/*-----------------------------------------------------------------------------
 * Interrupt management & service routines
 *---------------------------------------------------------------------------*/
//@ interrupt masking enable GPIO1;
void HAL_GPIO_Enable_IRQ1();

//@ interrupt service routine GPIO1;
void HAL_GPIO_ISR1()
{
    step_in_isr = true;

    bool state = HAL_GPIO_Read(1);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(10, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(10, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
}

//@ interrupt masking enable GPIO2;
void HAL_GPIO_Enable_IRQ2();

//@ interrupt service routine GPIO2;
void HAL_GPIO_ISR2()
{
    step_in_isr = true;

    bool state = HAL_GPIO_Read(2);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(10, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(10, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
}

/*-----------------------------------------------------------------------------
 * Application program
 *---------------------------------------------------------------------------*/
int main(void)
{
    HAL_GPIO_Init();
    HAL_GPIO_Enable_IRQ1();
    HAL_GPIO_Enable_IRQ2();

    int steps_in_app = 0;

    while (1) {
        assert(!step_in_isr);
        steps_in_app++;
        assert(!step_in_isr);
    }

    return 0;
}
