//#Safe
/*-----------------------------------------------------------------------------
 * Interrupt-Driven Program (IDP) for testing IDP verification
 *-----------------------------------------------------------------------------
 * Author: Manuel Bentele
 *   Date: 07.09.2026
 *---------------------------------------------------------------------------*/

#include <assert.h>
#include <stdbool.h>

/*-----------------------------------------------------------------------------
 * Type declarations
 *---------------------------------------------------------------------------*/
typedef enum event {
    EV_NONE,
    EV_GPIO
} event_t;

/*-----------------------------------------------------------------------------
 * Global variables
 *---------------------------------------------------------------------------*/
event_t ev = EV_NONE;

/*-----------------------------------------------------------------------------
 * Function declarations
 *---------------------------------------------------------------------------*/
void HAL_GPIO_Init(void);

/*-----------------------------------------------------------------------------
 * Interrupt management & service routines
 *---------------------------------------------------------------------------*/
//@ interrupt masking enable GPIO;
void HAL_GPIO_Enable_IRQ_A(void);

//@ interrupt masking enable GPIO;
void HAL_GPIO_Enable_IRQ_B(void);

//@ interrupt masking disable GPIO;
void HAL_GPIO_Disable_IRQ_A(void);

//@ interrupt masking disable GPIO;
void HAL_GPIO_Disable_IRQ_B(void);

//@ interrupt service routine GPIO;
void HAL_GPIO_ISR(void)
{
    ev = EV_GPIO;
}

/*-----------------------------------------------------------------------------
 * Application program
 *---------------------------------------------------------------------------*/
int main(void)
{
    HAL_GPIO_Init();

    assert(ev == EV_NONE);
    HAL_GPIO_Enable_IRQ_A();
    assert(ev == EV_NONE || ev == EV_GPIO);

    ev = EV_NONE;
    HAL_GPIO_Enable_IRQ_B();
    assert(ev == EV_NONE || ev == EV_GPIO);

    HAL_GPIO_Disable_IRQ_A();
    assert(ev == EV_NONE || ev == EV_GPIO);

    ev = EV_NONE;
    HAL_GPIO_Enable_IRQ_A();
    assert(ev == EV_NONE || ev == EV_GPIO);

    HAL_GPIO_Disable_IRQ_B();
    assert(ev == EV_NONE || ev == EV_GPIO);

    return 0;
}
