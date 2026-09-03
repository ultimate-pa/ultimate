// #SAFE
/*-----------------------------------------------------------------------------
 * Interrupt-Driven Program (IDP) for testing IDP verification
 *-----------------------------------------------------------------------------
 * Author: Matthias Zumkeller
 *   Date: 15.06.2026
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
int steps_in_app = 0;

/*-----------------------------------------------------------------------------
 * Function declarations
 *---------------------------------------------------------------------------*/
void HAL_GPIO_Init(void);
bool HAL_GPIO_Read(void);
void HAL_GPIO_Write(int pin, pin_state_t state);

/*-----------------------------------------------------------------------------
 * Interrupt management & service routines
 *---------------------------------------------------------------------------*/
//@ interrupt masking enable GPIO;
void HAL_GPIO_Enable_IRQ();

//@ interrupt service routine GPIO;
void HAL_GPIO_ISR()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read();
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(10, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(10, PIN_STATE_OFF);
        button_state = state;
    }

    int i = 0;
    while (i < 3) {
        i++;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

/*-----------------------------------------------------------------------------
 * Application program
 *---------------------------------------------------------------------------*/
int main(void)
{
    HAL_GPIO_Init();
    HAL_GPIO_Enable_IRQ();

    steps_in_app = 0;

    while (1) {
        assert(!step_in_isr);
        steps_in_app++;
        assert(!step_in_isr);
    }

    return 0;
}
