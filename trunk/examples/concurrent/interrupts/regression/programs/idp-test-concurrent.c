//#Safe
/*-----------------------------------------------------------------------------
 * Interrupt-Driven Program (IDP) for testing IDP verification
 *-----------------------------------------------------------------------------
 * Author: Matthias Zumkeller
 *   Date: 28.04.2026
 *---------------------------------------------------------------------------*/

#include <assert.h>
#include <pthread.h>
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
bool HAL_GPIO_Read(void);
void HAL_GPIO_Write(int pin, pin_state_t state);

/*-----------------------------------------------------------------------------
 * Interrupt management & service routines
 *---------------------------------------------------------------------------*/
//@ interrupt masking enable GPIO;
void HAL_GPIO_Enable_IRQ(void);

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
}

/*-----------------------------------------------------------------------------
 * Thread function definition
 *---------------------------------------------------------------------------*/
void *HAL_Thread(void *arg)
{
    int steps_in_thread = 0;

    while (steps_in_thread < 100) {
        assert(!step_in_isr);
        steps_in_thread++;
        assert(!step_in_isr);
    }

    return NULL;
}

/*-----------------------------------------------------------------------------
 * Application program
 *---------------------------------------------------------------------------*/
int main(void)
{
    HAL_GPIO_Init();
    HAL_GPIO_Enable_IRQ();

    pthread_t thread;
    pthread_create(&thread, NULL, HAL_Thread, NULL);

    return 0;
}
