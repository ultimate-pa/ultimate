//#Safe
#include <stdio.h>
#include <stdbool.h>

// Global state

bool button_state = false;

bool step_in_isr = false;

bool isr_executed = false;

// Function Prototypes
void HAL_GPIO_Init(void);
void HAL_GPIO_Enable_Int(void);
void HAL_GPIO_Disable_Int(void);
void isr_gpio(void);
bool HAL_GPIO_Read(void);
void HAL_GPIO_Write(int pin, int state);

// External or Mock Constants
#define BTN_PRESSED true
#define ON          1
#define OFF         0

int main(void) 
{
    
    HAL_GPIO_Init();
    HAL_GPIO_Enable_Int();

    int n = 0;
    while (n < 1000) {
        assert(!step_in_isr);
        n++;
        assert(!step_in_isr);
    }
    HAL_GPIO_Disable_Int();
    isr_executed = false;
    //n = 0;
    //while (n < 1000) {
        //n++;
    //}
    assert(isr_executed);
    return 0;
}

void HAL_GPIO_Enable_Int(void) 
{
    // ... logic ...
}

void HAL_GPIO_Disable_Int(void) 
{
    // ... logic ...
}

void isr_gpio(void) 
{   
    step_in_isr = true;
    bool st = HAL_GPIO_Read();
    if (st == BTN_PRESSED) {
        HAL_GPIO_Write(10, ON);
        button_state = st;
    } else {
        HAL_GPIO_Write(10, OFF);
        button_state = st;
    }
    step_in_isr  = false;  
   isr_executed = true;
}
