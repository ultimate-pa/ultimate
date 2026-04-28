//#Safe

#include <stdio.h>
#include <stdbool.h>

// Global state

bool button_state = false;

bool step_in_isr = false;

// Function Prototypes
void HAL_GPIO_Init(void);
void HAL_GPIO_Enable_Int1(void);
void HAL_GPIO_Enable_Int2(void);
void isr1_gpio(void);
void isr2_gpio(void);
bool HAL_GPIO_Read(int n);
void HAL_GPIO_Write(int pin, int state);

// External or Mock Constants
#define BTN_PRESSED true
#define ON          1
#define OFF         0

int main(void) 
{
    
    HAL_GPIO_Init();
    HAL_GPIO_Enable_Int1();
    HAL_GPIO_Enable_Int2();

    int n = 0;
    while (1) {
        assert(!step_in_isr);
        n++;
        assert(!step_in_isr);
    }

    return 0;
}

void HAL_GPIO_Enable_Int1(void) 
{
    // ... logic ...
}

void HAL_GPIO_Enable_Int2(void) 
{
    // ... logic ...
}

void isr1_gpio(void) 
{   
    step_in_isr = true;
    bool st = HAL_GPIO_Read(1);
    if (st == BTN_PRESSED) {
        HAL_GPIO_Write(10, ON);
        button_state = st;
    } else {
        HAL_GPIO_Write(10, OFF);
        button_state = st;
    }
    step_in_isr  = false;  
   
}

void isr2_gpio(void) 
{   
    step_in_isr = true;
    bool st = HAL_GPIO_Read(2);
    if (st == BTN_PRESSED) {
        HAL_GPIO_Write(20, ON);
        button_state = st;
    } else {
        HAL_GPIO_Write(20, OFF);
        button_state = st;
    }
    step_in_isr  = false;  
   
}
