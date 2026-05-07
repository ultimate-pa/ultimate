//#Safe
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

// Global state
bool button_state = false;
bool step_in_isr = false;

// Shared Constants
#define BTN_PRESSED true
#define ON          1
#define OFF         0

void HAL_GPIO_Init(void);
void HAL_GPIO_Write(int pin, int state);
bool HAL_GPIO_Read(int pin);

void isr1_gpio(void);

void HAL_GPIO_Enable_All_Int(void);

int main(void) 
{
    HAL_GPIO_Init();
    
    HAL_GPIO_Enable_All_Int();

    int n = 0;
    while (1) {
        assert(!step_in_isr);
        n++;
        assert(!step_in_isr);
        
        if(n > 1000) break; 
    }

    return 0;
}

void isr1_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(1);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(10, ON); button_state = st; }
    else { HAL_GPIO_Write(10, OFF); button_state = st; }
    step_in_isr = false;
}

void HAL_GPIO_Enable_All_Int(void) { /* logic... */ }

void HAL_GPIO_Init(void) {}
void HAL_GPIO_Write(int pin, int state) {}
bool HAL_GPIO_Read(int pin) { return false; }
