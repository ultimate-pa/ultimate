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

void isr1_gpio(void);  void isr2_gpio(void);  void isr3_gpio(void);
void isr4_gpio(void);  void isr5_gpio(void);  void isr6_gpio(void);
void isr7_gpio(void);  void isr8_gpio(void);  void isr9_gpio(void);
void isr10_gpio(void);

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

void isr2_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(2);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(20, ON); button_state = st; }
    else { HAL_GPIO_Write(20, OFF); button_state = st; }
    step_in_isr = false;
}

void isr3_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(3);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(30, ON); button_state = st; }
    else { HAL_GPIO_Write(30, OFF); button_state = st; }
    step_in_isr = false;
}

void isr4_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(4);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(40, ON); button_state = st; }
    else { HAL_GPIO_Write(40, OFF); button_state = st; }
    step_in_isr = false;
}

void isr5_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(5);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(50, ON); button_state = st; }
    else { HAL_GPIO_Write(50, OFF); button_state = st; }
    step_in_isr = false;
}

void isr6_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(6);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(60, ON); button_state = st; }
    else { HAL_GPIO_Write(60, OFF); button_state = st; }
    step_in_isr = false;
}

void isr7_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(7);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(70, ON); button_state = st; }
    else { HAL_GPIO_Write(70, OFF); button_state = st; }
    step_in_isr = false;
}

void isr8_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(8);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(80, ON); button_state = st; }
    else { HAL_GPIO_Write(80, OFF); button_state = st; }
    step_in_isr = false;
}

void isr9_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(9);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(90, ON); button_state = st; }
    else { HAL_GPIO_Write(90, OFF); button_state = st; }
    step_in_isr = false;
}

void isr10_gpio(void) {
    step_in_isr = true;
    bool st = HAL_GPIO_Read(10);
    if (st == BTN_PRESSED) { HAL_GPIO_Write(100, ON); button_state = st; }
    else { HAL_GPIO_Write(100, OFF); button_state = st; }
    step_in_isr = false;
}

void HAL_GPIO_Enable_All_Int(void) { /* logic... */ }

void HAL_GPIO_Init(void) {}
void HAL_GPIO_Write(int pin, int state) {}
bool HAL_GPIO_Read(int pin) { return false; }
