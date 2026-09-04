//#Safe
/*-----------------------------------------------------------------------------
 * Interrupt-Driven Program (IDP) for testing IDP verification
 *-----------------------------------------------------------------------------
 * Author: Matthias Zumkeller
 *   Date: 24.06.2026
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
bool isr_executed = false;

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
void HAL_GPIO_Enable_IRQ(void);

//@ interrupt masking disable GPIO;
void HAL_GPIO_Disable_IRQ(void);

//@ interrupt service routine GPIO;
void HAL_GPIO_ISR(void)
{
    step_in_isr = true;

    bool state = HAL_GPIO_Read();
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(10, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(10, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    isr_executed = true;
}

/*-----------------------------------------------------------------------------
 * Application program
 *---------------------------------------------------------------------------*/
int main(void)
{
    HAL_GPIO_Init();
    HAL_GPIO_Enable_IRQ();

    int steps_in_app = 0;

    while (steps_in_app < 250) {
        assert(!step_in_isr);
        steps_in_app++;
        assert(!step_in_isr);
    }

    HAL_GPIO_Disable_IRQ();
    isr_executed = false;

    steps_in_app = 0;
    while (steps_in_app < 1000) {
        steps_in_app++;
    }
    assert(!isr_executed);

    return 0;
}
