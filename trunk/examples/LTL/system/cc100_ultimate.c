bool					buff_uebergabe;         // 1:RxD-Empfangsbuffer soll in Zwischenpuffer uebernommen werden
bool					bald_low_batt;          // 1: F.KO-Batterien nur noch <= 20 Std    
bool					trigger_led;            // 1:Triggerbit fuer Notstom-LED  
unsigned char			timer_batt;             // Zeitgeber fuer Batteriehandling Zeitbasis 1s
unsigned char			timer_10ms;             // Zeitgeber mit 10ms Zeitbasis    
bool					bit_relais_lock;
unsigned char			h_byte_10s;				// Hilfsbyte 10s-Zaehler
bool					h_bit;					// Hilfsbit fuer Erzeugung eines 10ms Zeit-Intervalls
unsigned char			h_byte;					// Hilfsbyte 10ms-Zaehler
unsigned char			h_byte_s;				// Hilfsbyte 1s-Zaehler  
unsigned char			timer_s;				// Sekundentimer definieren 

volatile unsigned char ADS, MK0, MK1;
volatile bool ADIF, ADCS, RTS, DCD, TESTBATT, CLK, DATA, TCE0, LC2;
volatile unsigned int ADCR;

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
	backing_member unsigned char     byte; 
};       
typedef union sregister_2 hc_595_2 ;

hc_595_2 relais;




#define _ch_1                           0x01                    // Analogeingang 1 selektieren
#define _min_val_batt                   33152                   // 10,6V UBATT -> 1,266V am ADC -> Wert 259 (x128)  //ATP:33152
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

/*@
  @ ensures \result == ADCR;
  @ ensures \result <= 65535;
  @*/
unsigned int convert_ad(unsigned char kanal)
{
	unsigned char ucMK0_Bak, ucMK1_Bak;
	ADIF  = 0;       // Loesche Interruptflag des AD-Wandlers
	ADS   = kanal;   // SFR ADS0 setzen
	ADCS  = 1;       // Starte kontinuierliche Wandlung
	
	_DI();           // Interrupts sperren

	ucMK0_Bak=GET_INTR_STATUS0;
	DISABLE_INTR_STATUS0(MK0_INTR_PROT);

	ucMK1_Bak=GET_INTR_STATUS1;
	DISABLE_INTR_STATUS1(MK1_INTR_PROT);

	ADIF  = 0;       // Ersten Wert verwerfen
	
	ADCS  = 0;       // Stoppe A/D-Wandler

	_EI();           // Interrupts wiederherstellen

	SET_INTR_STATUS0(ucMK0_Bak); 
	SET_INTR_STATUS1(ucMK1_Bak);

	return ADCR; 
}

/*@
  @ ensures \result == ADCR;
  @ ensures bald_low_batt == 1 <==> last_ADCR < 33152;
  @*/
void test_battery(void)
{
    unsigned int k;
    // Batterielast zuschalten, kurze Einschwingzeit        
    TESTBATT = 1;

    // A/D-Wandlung
    k = convert_ad(_ch_1);    

    // Batterielast wieder trennen
    TESTBATT = 0;
    
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

void sio_hc595(unsigned char a_byte)
{               
    CLK = DATA = 0;                                                             // Startzustand herstellen
    if (a_byte & 0x80)                                                          // Zuerst Bit 7 -> QH Pin 7
        DATA = 1;                                                               // DATA auf 1 falls erforderlich
    CLK = 1;                                                                    // Steigende Flanke uebernimmt
    CLK = DATA = 0;                                                             // DATA wieder auf 0 setzen
    if (a_byte & 0x40)                                                          // dann Bit 6 -> QG Pin 6
        DATA = 1;
    CLK = 1;
    CLK = DATA = 0;
    if (a_byte & 0x20)                                                          // dann Bit 5 -> QF Pin 5
        DATA = 1;
    CLK = 1;
    CLK = DATA = 0;
    if (a_byte & 0x10)                                                          // dann Bit 4 -> QE Pin 4
        DATA = 1;
    CLK = 1;
    CLK = DATA = 0;
    if (a_byte & 0x08)                                                          // dann Bit 3 -> QD Pin 3
        DATA = 1;
    CLK = 1;
    CLK = DATA = 0;
    if (a_byte & 0x04)                                                          // dann Bit 2 -> QC Pin 2
        DATA = 1;
    CLK = 1;
    CLK = DATA = 0;
    if (a_byte & 0x02)                                                          // dann Bit 1 -> QB Pin 1
        DATA = 1;
    CLK = 1;
    CLK = DATA = 0;
    if (a_byte & 0x01)                                                          // Zuletzt Bit 0 -> QA Pin 15
        DATA = 1;                                                               // DATA auf 1 falls erforderlich
    CLK = 1;                                                                    // Steigende Flanke uebernimmt
    DATA = 1;                                                                   // Mit Ruhezustand verlassen
}

/*@ 
  @ requires bald_low_batt == 1 <==> last_ADCR < 33152;
  @ requires h_byte_10s <=10;
  @ requires h_byte_s <=10;
  @ requires h_byte <=10;
  @ requires trigger_led == 0;
  @ ensures h_byte_10s <=10;
  @ ensures h_byte_s <=10;
  @ ensures h_byte <=10;
  @ ensures trigger_led == 0;
  @*/
void timer(void)
{
	/*
#############################################################################
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
    TCE0 = 0;                     
    TCE0 = 1;                     

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
			assert(relais.bits.led_notstrom == 1 ==> ADCR < 33152);
            trigger_led = 0;

             /* ==== Relais, Hupe und LED Stoerung, Notstrom + Betrieb bedienen ==== */
            if (bit_relais_lock == 0) 
			{
                sio_hc595(relais.byte);  

                // In das Ausgangsregister uebernehmen
                LC2 = 0;
                LC2 = 1;
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

void main()
{
	//Initialization
	h_byte=0;
	h_byte_s=0;
	timer_s=0;
	h_byte_10s = 0;
	relais.byte = 0;
	assert(relais.bits.led_notstrom == 1 ==> ADCR < 33152);
	trigger_led = 0;

	sio_hc595(0); 

	LC2 = 0;              
	LC2 = 1;  
	bit_relais_lock = 0;
	h_bit=0;

	TCE0 = 1;

	test_battery();

	//Main loop
	/*@ loop invariant h_byte_10s <= 10;
	  @ loop invariant h_byte_s <= 10;
	  @ loop invariant h_byte <= 10;
	  @ loop invariant bald_low_batt ==1 ==> ADCR < 33152;
	  @ loop invariant trigger_led == 0;
	  @*/
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

