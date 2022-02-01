#include "verification.h"

//necessary because original program does not include stdbool.h (compiler intrinsic) 
#define bool _Bool


_(ghost unsigned int last_ADCR;)

bool					bald_low_batt;          // 1: F.KO-Batterien nur noch <= 20 Std    
bool					trigger_led;            // 1: Triggerbit fuer Notstom-LED  
unsigned char			timer_batt;             // Zeitgeber fuer Batteriehandling Zeitbasis 1s
unsigned char			timer_10ms;             // Zeitgeber mit 10ms Zeitbasis    
bool					bit_relais_lock;
unsigned char			h_byte_10s;				// Hilfsbyte 10s-Zaehler
bool					h_bit;					// Hilfsbit fuer Erzeugung eines 10ms Zeit-Intervalls
unsigned char			h_byte;					// Hilfsbyte 10ms-Zaehler
unsigned char			h_byte_s;				// Hilfsbyte 1s-Zaehler  
unsigned char			timer_s;				// Sekundentimer definieren 

DECL_VOLATILE(unsigned char,ADS)
DECL_VOLATILE(unsigned char,MK0)
DECL_VOLATILE(unsigned char,MK1)
DECL_VOLATILE(bool,ADIF)
DECL_VOLATILE(bool,ADCS)
DECL_VOLATILE(bool,RTS)
DECL_VOLATILE(bool,DCD)
DECL_VOLATILE(bool,TESTBATT)
DECL_VOLATILE(bool,CLK)
DECL_VOLATILE(bool,DATA)
DECL_VOLATILE(bool,TCE0)
DECL_VOLATILE(bool,LC2)

//~2,5V (eigentlich 10bit wert, wobei die word-codierung 0 d9 d8 d7 d6 d5 d4 d3 d2 d1 d0 0 0 0 0 0 , 
// comment zu test_batt in org program:
// Unterprogramm fuer den Batterietest.                                     
// Die Last wird fuer ca. 100us zugeschaltet, die Eingangsspannung ist      
// immer < 2,5V, somit d9 immer 0.
DECL_VOLATILE_INV(unsigned int,ADCR,ADCR<=32767 && ADCR % 16 == 0) 

union sregister_2
{
	struct
	{
		unsigned char  rel_1:1;                                // Bit0: Relais 1 zieht an mit 1     
		unsigned char  rel_2:1;                                // Bit1: Relais 2 zieht an mit 1
		unsigned char  rel_3:1;                                // Bit2: Relais 3 zieht an mit 1
		unsigned char  rel_4:1;                                // Bit3: Relais 4 zieht an mit 1
		unsigned char  hupe:1;                                 // Bit4: Hupe
		unsigned char  led_stoer:1;                            // Bit5: LED Stoerung
		unsigned char  led_notstrom:1;                         // Bit6: LED Notstrom
		unsigned char  led_betrieb:1;                          // Bit7: LED Betrieb
	} bits;  
	struct
	{
		unsigned char  rels:4;
		unsigned char  led_hupe:4;
	} bits_hupe;  
	_(backing_member) unsigned char     byte; 
};       
typedef union sregister_2 hc_595_2 ;

hc_595_2 relais;

#define _ch_1                           0x01                    // Analogeingang 1 selektieren
#define _min_val_batt                   33152                   // 10,6V UBATT -> 1,266V am ADC -> Wert 259 (x128)  //ATP:33152 , die /2 ist bereits integriert, ADCR ist ein 10Bit Wert
#define _leer_val_batt                  22784                   // 7,5V  UBATT -> 0,87V  am ADC -> Wert 178 (x128) //ATP:22784
#define _test_batt                      10                      // 10 x 1s Zeitraster fuer Batteriepruefungen 
#define MK0_INTR_WATCH              0x80    // INTWT Watch timer
#define MK0_INTR_TXD                0x40    // INTST TxD-Interrupt
#define MK0_INTR_PF                 0x02    // INTP0 (PF Eingang)
#define MK1_INTR_TM0                0x02    // INTTM0 TM0 Interrupt
#define MK1_INTR_WTI                0x01    // INTWTI Intervall timer
#define SYNC_MAIN_LOOP_RUNTIME_MS   3
#define SYNC_RXD_TIMEOUT_VALUE_MS   500 

#define DISABLE_INTR_STATUS0(x) MK0 |= (x)
#define DISABLE_INTR_STATUS1(x) MK1 |= (x)
#define ENABLE_INTR_STATUS0(x)  MK0 &= ~(x)
#define ENABLE_INTR_STATUS1(x)  MK1 &= ~(x)
#define GET_INTR_STATUS0        MK0
#define GET_INTR_STATUS1        MK1

#define SYNC_RXD_TIMEOUT_VALUE      (SYNC_RXD_TIMEOUT_VALUE_MS/SYNC_MAIN_LOOP_RUNTIME_MS)
#define MK0_INTR_PROT           (MK0_INTR_WATCH | MK0_INTR_TXD | MK0_INTR_PF)
#define MK1_INTR_PROT           (MK1_INTR_TM0 | MK1_INTR_WTI)
#define SET_INTR_STATUS0(x)     MK0 = (x)
#define SET_INTR_STATUS1(x)     MK1 = (x)

void _DI(void) { }
void _EI(void) { }


unsigned int ad_convert(unsigned char kanal 
DECLARE_CLAIM_ON(ADIF) 
DECLARE_CLAIM_ON(ADS) 
DECLARE_CLAIM_ON(ADCS) 
DECLARE_CLAIM_ON(ADCR)
DECLARE_CLAIM_ON(MK0)
DECLARE_CLAIM_ON(MK1))
ACCESSES_VOLATILE(ADIF)
ACCESSES_VOLATILE(ADS)
ACCESSES_VOLATILE(ADCS)
ACCESSES_VOLATILE(ADCR)
ACCESSES_VOLATILE(MK0)
ACCESSES_VOLATILE(MK1)
_(ensures \result == ADCR)
_(ensures \result <= 65535)
{
	unsigned char ucMK0_Bak, ucMK1_Bak;
	WRITE_VOLATILE(ADIF,ADIF = 0;)		// Loesche Interruptflag des AD-Wandlers
	WRITE_VOLATILE(ADS,ADS = kanal;)	// SFR ADS0 setzen
	WRITE_VOLATILE(ADCS,ADCS = 1;)		// Starte kontinuierliche Wandlung
	
	while(READ_VOLATILE(ADIF,ADIF == 0)){} // Warte bis A/D-Wandler fertig ist (ca. 14us)
	
	_DI();           			// Interrupts sperren

	ucMK0_Bak=READ_VOLATILE(MK0,GET_INTR_STATUS0);
	WRITE_VOLATILE(MK0,DISABLE_INTR_STATUS0(MK0_INTR_PROT);)

	ucMK1_Bak=READ_VOLATILE(MK1,GET_INTR_STATUS1);
	WRITE_VOLATILE(MK1,DISABLE_INTR_STATUS1(MK1_INTR_PROT);)

	WRITE_VOLATILE(ADIF,ADIF = 0;)	// Ersten Wert verwerfen
	
	while(READ_VOLATILE(ADIF,ADIF == 0)){}	// Auf zweiten Wert warten
	
	WRITE_VOLATILE(ADCS,ADCS = 0;)		// Stoppe A/D-Wandler

	_EI();           			// Interrupts wiederherstellen
	
	WRITE_VOLATILE(MK0,SET_INTR_STATUS0(ucMK0_Bak);)
	WRITE_VOLATILE(MK1,SET_INTR_STATUS1(ucMK1_Bak);)
	
	return READ_VOLATILE(ADCR,ADCR);
}

void test_batt(
DECLARE_CLAIM_ON(TESTBATT)	
DECLARE_CLAIM_ON(ADIF)
DECLARE_CLAIM_ON(ADS)
DECLARE_CLAIM_ON(ADCS)
DECLARE_CLAIM_ON(ADCR)
DECLARE_CLAIM_ON(MK0)
DECLARE_CLAIM_ON(MK1)
)
ACCESSES_VOLATILE(TESTBATT)
ACCESSES_VOLATILE(ADIF)
ACCESSES_VOLATILE(ADS)
ACCESSES_VOLATILE(ADCS)
ACCESSES_VOLATILE(ADCR)
ACCESSES_VOLATILE(MK0)
ACCESSES_VOLATILE(MK1)
_(writes &bald_low_batt)
_(writes &last_ADCR)
_(ensures bald_low_batt == 1 <==> last_ADCR < 33152)
{
    unsigned int k;
    // Batterielast zuschalten, kurze Einschwingzeit        
    WRITE_VOLATILE(TESTBATT,TESTBATT = 1;)

    // A/D-Wandlung
    k = ad_convert(_ch_1 
		PASS_CLAIM_ON(ADIF) 
		PASS_CLAIM_ON(ADS) 
		PASS_CLAIM_ON(ADCS) 
		PASS_CLAIM_ON(ADCR)
		PASS_CLAIM_ON(MK0)
		PASS_CLAIM_ON(MK1)
	);

	//zweite Wandlung
	k += ad_convert(_ch_1 
		PASS_CLAIM_ON(ADIF) 
		PASS_CLAIM_ON(ADS) 
		PASS_CLAIM_ON(ADCS) 
		PASS_CLAIM_ON(ADCR)
		PASS_CLAIM_ON(MK0)
		PASS_CLAIM_ON(MK1)
	);
	_(ghost last_ADCR = k;)
    // Batterielast wieder trennen
    WRITE_VOLATILE(TESTBATT,TESTBATT = 0;)
    
    // Vergleich mit Vergleichswert linksbuendig 
    if(k < _min_val_batt)
    { 
        bald_low_batt = 1; // Batterie ist in schlechtem Ladezustand		
    }    
    else
    {
		bald_low_batt = 0; // Batterie ist noch in Ordnung   
    }
}


/*
vcc sample_battery.c /F:sio_hc595 /sm /st
Verification of sio_hc595 (smoke:0) (6) (7) (8) (9) (10) (12) [9,14s] succeeded.
Time: 9,31s total, 0,17s compiler, 0,00s Boogie, 9,14s method verification.

12.09.10 14:56
*/
void sio_hc595(unsigned char a_byte 
DECLARE_CLAIM_ON(CLK)
DECLARE_CLAIM_ON(DATA)
)
ACCESSES_VOLATILE(CLK)
ACCESSES_VOLATILE(DATA)
{
	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
	if (a_byte & 0x80){ 				// Zuerst Bit 7 -> QH Pin 7
		WRITE_VOLATILE(DATA,DATA = 1;)
	}
	WRITE_VOLATILE(CLK,CLK = 1;)
    
	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
    if (a_byte & 0x40){				// dann Bit 6 -> QG Pin 6
        WRITE_VOLATILE(DATA,DATA = 1;)
	}
    WRITE_VOLATILE(CLK,CLK = 1;)

	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
    if (a_byte & 0x20){				// dann Bit 5 -> QF Pin 5
		WRITE_VOLATILE(DATA,DATA = 1;)
	}
    WRITE_VOLATILE(CLK,CLK = 1;)

	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
    if (a_byte & 0x10){				// dann Bit 4 -> QE Pin 4
        WRITE_VOLATILE(DATA,DATA = 1;)
	}
    WRITE_VOLATILE(CLK,CLK = 1;)

	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
    if (a_byte & 0x08){				// dann Bit 3 -> QD Pin 3
        WRITE_VOLATILE(DATA,DATA = 1;)
	}
    WRITE_VOLATILE(CLK,CLK = 1;)

	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
    if (a_byte & 0x04){       		// dann Bit 2 -> QC Pin 2
        WRITE_VOLATILE(DATA,DATA = 1;)
	}
    WRITE_VOLATILE(CLK,CLK = 1;)

	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
    if (a_byte & 0x02){   			// dann Bit 1 -> QB Pin 1
        WRITE_VOLATILE(DATA,DATA = 1;)
	}
    WRITE_VOLATILE(CLK,CLK = 1;)

	WRITE_VOLATILE(CLK,CLK = 0;)
	WRITE_VOLATILE(DATA,DATA = 0;)
    if (a_byte & 0x01){   			// Zuletzt Bit 0 -> QA Pin 15
        WRITE_VOLATILE(DATA,DATA = 1;)     
	}
    WRITE_VOLATILE(CLK,CLK = 1;)
    
	WRITE_VOLATILE(DATA,DATA = 1;)   
}

void timer_5ms(
DECLARE_CLAIM_ON(TCE0)
DECLARE_CLAIM_ON(LC2)
DECLARE_CLAIM_ON(CLK)
DECLARE_CLAIM_ON(DATA)
	)
ACCESSES_VOLATILE(TCE0)
ACCESSES_VOLATILE(LC2)
ACCESSES_VOLATILE(CLK)
ACCESSES_VOLATILE(DATA)
_(writes &timer_10ms,&h_bit,&h_byte,&h_byte_s,&h_byte_10s,&trigger_led,&relais.byte,&timer_batt)
_(requires \thread_local(&bald_low_batt))
_(requires \thread_local(&last_ADCR))
_(requires \thread_local(&bit_relais_lock))
_(requires bald_low_batt == 1 <==> last_ADCR < 33152)
_(maintains h_byte_10s <=10)
_(maintains h_byte_s <=10)
_(maintains h_byte <=10)
_(maintains trigger_led == 0)
{
	/*
#############################################################################
#                                                                           #
# timer_5ms()                                                               #
#                                                                           #
# Interrupt-Routine mit 5ms-Zeit-Intervall                                  #
#                                                                           #
# Bearbeitet verschiedene Timer im Zeitraster 10ms, 100ms,....              #
# Hier erfolgt auch alle 100ms die Ansteuerung von Relais, Hupe und         #
# LED Stoerung, Notstrom und Betrieb.                                       #
#                                                                           #
#############################################################################
*/


    // Stoppe und loesche Timer TM0, Neustart Timer TM0                
    WRITE_VOLATILE(TCE0,TCE0 = 0;)
    WRITE_VOLATILE(TCE0,TCE0 = 1;)

    // Toggle-Bit um aus einem 5ms-Intervall ein 10ms-Intervall zu machen (nur jedes zweite mal werden die Timer bearbeitet)
	if(h_bit==0)
	{
		
		h_bit=1;
	} 
	else 
	{
		
		h_bit=0;
	}

    /*
    ==== Pruefe ob ein 10ms-Zeitintervall erreicht ist ====
    */
    if(h_bit)
    {

        /* =================== 10ms Bereich ================ */

        // Interner 10ms Zaehler erhoehen 
        h_byte++;                   

		if(timer_10ms)
		{  
			
            timer_10ms--;
		}

        /* ==== Pruefe ob ein 100ms-Zeitintervall erreicht ist ==== */
        if(h_byte >= 10)
        {  
            // Interner 100ms-Zaehler loeschen 
            h_byte = 0; 

            // Interne Sekundenzaehler alle 100ms erhoehen
            h_byte_s++;

            // Notstrom-Led ein  
			if(bald_low_batt == 1)
			{
				trigger_led = 1;
			}
            relais.bits.led_notstrom = trigger_led;
			_(assert relais.bits.led_notstrom == 1 <==> last_ADCR < 33152)
            trigger_led = 0;

             /* ==== Relais, Hupe und LED Stoerung, Notstrom + Betrieb bedienen ==== */
            if (bit_relais_lock == 0) 
			{
                sio_hc595(relais.byte
					PASS_CLAIM_ON(CLK) 
					PASS_CLAIM_ON(DATA)
				); 

                // In das Ausgangsregister uebernehmen
                WRITE_VOLATILE(LC2,LC2 = 0;)
                WRITE_VOLATILE(LC2,LC2 = 1;)
            }


            if(h_byte_s >= 10)
            {       
                /* ================ Sekunden-Bereich ================= */

                // Interner Sekunden-Zaehler loeschen 
                h_byte_s = 0;             

                // Timer 10s Intervall
                h_byte_10s++;

                if(h_byte_10s>=10)
				{
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

void program(
DECLARE_CLAIM_ON(CLK)
DECLARE_CLAIM_ON(DATA)
DECLARE_CLAIM_ON(LC2)
DECLARE_CLAIM_ON(TCE0)
DECLARE_CLAIM_ON(TESTBATT)
DECLARE_CLAIM_ON(ADIF)
DECLARE_CLAIM_ON(ADS)
DECLARE_CLAIM_ON(ADCS)
DECLARE_CLAIM_ON(ADCR)
DECLARE_CLAIM_ON(MK0)
DECLARE_CLAIM_ON(MK1)	
)
_(writes &bald_low_batt, &trigger_led, &timer_batt, &timer_10ms, &bit_relais_lock, &h_byte_10s, &h_bit, &h_byte, &h_byte_s, &timer_s, \span(&relais))
_(writes &last_ADCR)
ACCESSES_VOLATILE(CLK)
ACCESSES_VOLATILE(DATA)
ACCESSES_VOLATILE(LC2)
ACCESSES_VOLATILE(TCE0)
ACCESSES_VOLATILE(TESTBATT)
ACCESSES_VOLATILE(ADIF)
ACCESSES_VOLATILE(ADS)
ACCESSES_VOLATILE(ADCS)
ACCESSES_VOLATILE(ADCR)
ACCESSES_VOLATILE(MK0)
ACCESSES_VOLATILE(MK1)
{
	//Initialization
	_(ghost last_ADCR = 33153)
	h_byte=0;
	h_byte_s=0;
	timer_s=0;
	h_byte_10s = 0;
	relais.byte = 0;
	_(assert relais.bits.led_notstrom == 1 <==> last_ADCR < 33152)
	trigger_led = 0;

	sio_hc595(0 
		PASS_CLAIM_ON(CLK) 
		PASS_CLAIM_ON(DATA)
		); 

	WRITE_VOLATILE(LC2,LC2 = 0;)              
	WRITE_VOLATILE(LC2,LC2 = 1;)
	
	bit_relais_lock = 0;
	h_bit=0;
	
	WRITE_VOLATILE(TCE0,TCE0 = 1;)	

	test_batt(
		PASS_CLAIM_ON(TESTBATT)	
		PASS_CLAIM_ON(ADIF)
		PASS_CLAIM_ON(ADS)
		PASS_CLAIM_ON(ADCS)
		PASS_CLAIM_ON(ADCR)
		PASS_CLAIM_ON(MK0)
		PASS_CLAIM_ON(MK1)	
	);

	//Main loop
	while(1)
	_(invariant \mutable(&relais.byte))
	_(invariant h_byte_10s <= 10)
	_(invariant h_byte_s <= 10)
	_(invariant h_byte <= 10)
	_(invariant bald_low_batt ==1 <==> last_ADCR < 33152)
	_(invariant trigger_led == 0)
	{
		timer_5ms(
			PASS_CLAIM_ON(TCE0)
			PASS_CLAIM_ON(LC2)
			PASS_CLAIM_ON(CLK)
			PASS_CLAIM_ON(DATA)			
		);

		// Ist es Zeit zur Ueberpruefung der Notstrom-Batterie ?
		if(timer_batt == 0)
		{
			// Batterietest --> Batterie-Status aktuallisieren
			test_batt(
				PASS_CLAIM_ON(TESTBATT)	
				PASS_CLAIM_ON(ADIF)
				PASS_CLAIM_ON(ADS)
				PASS_CLAIM_ON(ADCS)
				PASS_CLAIM_ON(ADCR)
				PASS_CLAIM_ON(MK0)
				PASS_CLAIM_ON(MK1)	
			);
			timer_batt = _test_batt; // Zeit bis zur naechsten Pruefung in den Timer laden   
		}
		_(assert timer_batt != 0)
	}
}

void main(void)
CREATES_CLAIM_ON(CLK)
CREATES_CLAIM_ON(DATA)
CREATES_CLAIM_ON(LC2)
CREATES_CLAIM_ON(TCE0)
CREATES_CLAIM_ON(TESTBATT)
CREATES_CLAIM_ON(ADIF)
CREATES_CLAIM_ON(ADS)
CREATES_CLAIM_ON(ADCS)
CREATES_CLAIM_ON(ADCR)
CREATES_CLAIM_ON(MK0)
CREATES_CLAIM_ON(MK1)
_(writes &bald_low_batt, &trigger_led, &timer_batt, &timer_10ms, &bit_relais_lock, &h_byte_10s, &h_bit, &h_byte, &h_byte_s, &timer_s, \span(&relais))
_(writes &last_ADCR)
{
	_(assert UCHAR_MAX == 255)

	DECLARE_CLAIM_ON(CLK)
	DECLARE_CLAIM_ON(DATA)
	DECLARE_CLAIM_ON(LC2)
	DECLARE_CLAIM_ON(TCE0)
	DECLARE_CLAIM_ON(TESTBATT)
	DECLARE_CLAIM_ON(ADIF)
	DECLARE_CLAIM_ON(ADS)
	DECLARE_CLAIM_ON(ADCS)
	DECLARE_CLAIM_ON(ADCR)
	DECLARE_CLAIM_ON(MK0)
	DECLARE_CLAIM_ON(MK1)

	CREATE_CLAIM_ON(CLK)
	CREATE_CLAIM_ON(DATA)
	CREATE_CLAIM_ON(LC2)
	CREATE_CLAIM_ON(TCE0)
	CREATE_CLAIM_ON(TESTBATT)
	CREATE_CLAIM_ON(ADIF)
	CREATE_CLAIM_ON(ADS)
	CREATE_CLAIM_ON(ADCS)
	CREATE_CLAIM_ON(ADCR)
	CREATE_CLAIM_ON(MK0)
	CREATE_CLAIM_ON(MK1)
	
	program(
		PASS_CLAIM_ON(CLK)
		PASS_CLAIM_ON(DATA)
		PASS_CLAIM_ON(LC2)
		PASS_CLAIM_ON(TCE0)
		PASS_CLAIM_ON(TESTBATT)
		PASS_CLAIM_ON(ADIF)
		PASS_CLAIM_ON(ADS)
		PASS_CLAIM_ON(ADCS)
		PASS_CLAIM_ON(ADCR)
		PASS_CLAIM_ON(MK0)
		PASS_CLAIM_ON(MK1)
	);
}