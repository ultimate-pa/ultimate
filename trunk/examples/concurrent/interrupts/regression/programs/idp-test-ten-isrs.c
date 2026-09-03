// #SAFE
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
int steps_in_app = 0;

/*-----------------------------------------------------------------------------
 * Function declarations
 *---------------------------------------------------------------------------*/
void HAL_GPIO_Init(void);
bool HAL_GPIO_Read(int pin);
void HAL_GPIO_Write(int pin, pin_state_t state);

/*-----------------------------------------------------------------------------
 * Interrupt management & service routines
 *---------------------------------------------------------------------------*/
//@ interrupt masking enable \all;
void HAL_GPIO_Enable_IRQ_All();

//@ interrupt service routine GPIO1;
void HAL_GPIO_ISR1()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(1);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(11, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(11, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO2;
void HAL_GPIO_ISR2()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(2);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(12, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(12, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO3;
void HAL_GPIO_ISR3()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(3);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(13, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(13, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO4;
void HAL_GPIO_ISR4()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(4);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(14, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(14, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO5;
void HAL_GPIO_ISR5()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(5);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(15, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(15, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO6;
void HAL_GPIO_ISR6()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(6);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(16, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(16, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO7;
void HAL_GPIO_ISR7()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(7);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(17, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(17, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO8;
void HAL_GPIO_ISR8()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(8);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(18, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(18, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO9;
void HAL_GPIO_ISR9()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(9);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(19, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(19, PIN_STATE_OFF);
        button_state = state;
    }

    step_in_isr = false;
    assert(steps_in_app == old_steps_in_app);
}

//@ interrupt service routine GPIO10;
void HAL_GPIO_ISR10()
{
    int old_steps_in_app = steps_in_app;
    step_in_isr = true;

    bool state = HAL_GPIO_Read(10);
    if (state == BTN_PRESSED) {
        HAL_GPIO_Write(20, PIN_STATE_ON);
        button_state = state;
    } else {
        HAL_GPIO_Write(20, PIN_STATE_OFF);
        button_state = state;
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
    HAL_GPIO_Enable_IRQ_All();

    steps_in_app = 0;

    while (1) {
        assert(!step_in_isr);
        steps_in_app++;
        assert(!step_in_isr);

        if (steps_in_app > 1000) {
            break;
        }
    }

    return 0;
}
