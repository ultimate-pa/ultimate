#define bool _Bool

//@ ltl invariant positive: [](AP(ADCR < 33152) ==> <>(AP(bald_low_batt == 1)));

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

bool					bald_low_batt;          // 1: F.KO-Batterien nur noch <= 20 Std    
unsigned char			timer_batt;             // Zeitgeber fuer Batteriehandling Zeitbasis 1s
unsigned char			timer_10ms;             // Zeitgeber mit 10ms Zeitbasis    
unsigned char			h_byte_10s;				// Hilfsbyte 10s-Zaehler
bool					h_bit;					// Hilfsbit fuer Erzeugung eines 10ms Zeit-Intervalls
unsigned char			h_byte;					// Hilfsbyte 10ms-Zaehler
unsigned char			h_byte_s;				// Hilfsbyte 1s-Zaehler  
unsigned char			timer_s;				// Sekundentimer definieren 

volatile bool TESTBATT;
volatile unsigned int ADCR;

#define _min_val_batt                   33152                   // 10,6V UBATT -> 1,266V am ADC -> Wert 259 (x128)  //ATP:33152
#define _leer_val_batt                  22784                   // 7,5V  UBATT -> 0,87V  am ADC -> Wert 178 (x128) //ATP:22784
#define _test_batt                      10                      // 10 x 1s Zeitraster fuer Batteriepruefungen 

unsigned int convert_ad()
{
	//hole irgendeinen ADCR Wert 
	ADCR = __VERIFIER_nondet_int();
	__VERIFIER_assume(ADCR < 65535); 
	return ADCR; 
}

void test_battery(void)
{
    unsigned int k;
    // Batterielast zuschalten, kurze Einschwingzeit        
    TESTBATT = 1;

    // A/D-Wandlung
    k = convert_ad();    
	
    // Batterielast wieder trennen
    TESTBATT = 0;
    
    // Vergleich mit Vergleichswert linksbuendig 
    if(k < _min_val_batt) { 
        bald_low_batt = 1; // Batterie ist in schlechtem Ladezustand
    } else {
		bald_low_batt = 0; // Batterie ist noch in Ordnung   
    }
}

void timer(void)
{
    // Toggle-Bit um aus einem 5ms-Intervall ein 10ms-Intervall zu machen (nur jedes zweite mal werden die Timer bearbeitet)
	if(h_bit==0) {
		h_bit=1;
	} else {
		h_bit=0;
	}

    //Pruefe ob ein 10ms-Zeitintervall erreicht ist
    if(h_bit) {
        // Interner 10ms Zaehler erhoehen 
        h_byte++;                   

		if(timer_10ms) {  
            timer_10ms--;
		}

        // Pruefe ob ein 100ms-Zeitintervall erreicht ist
        if(h_byte >= 10) {  
            // Interner 100ms-Zaehler loeschen 
            h_byte = 0; 

            // Interne Sekundenzaehler alle 100ms erhoehen
            h_byte_s++;
		
			// Pruefe ob ein 1s-Zeitintervall erreicht ist		
            if(h_byte_s >= 10) {       
                // Interner 1s-Zaehler loeschen 
                h_byte_s = 0;             

                // Timer 10s Intervall
                h_byte_10s++;

				// Pruefe ob ein 10s-Zeitintervall erreicht ist		
                if(h_byte_10s>=10)
				{
					// Interner 10s-Zaehler loeschen 
                    h_byte_10s=0;
                }

                // Timer fuer das Batteriepruefungs-Intervall     
				if(timer_batt)
				{        
					timer_batt--;
				}
            }      
        }
    }  
}

void main()
{
	//Initialization
	h_byte=0;
	h_byte_s=0;
	timer_s=0;
	h_byte_10s = 0;
	h_bit=0;
	timer_batt=0;

	test_battery();

	//Main loop
	while(1)
	{
		timer();

		// Ist es Zeit zur Ueberpruefung der Notstrom-Batterie ?
		if(timer_batt == 0)
		{
			// Batterietest --> Batterie-Status aktuallisieren
			test_battery();

			timer_batt = _test_batt; // Zeit bis zur naechsten Pruefung in den Timer laden   
		}
	}
}