#include <stdio.h> 
#include <assert.h>
#include <math.h>
#include <stdlib.h>
#include <stdarg.h>

///////////////////////////////////////////////////////////////////////////////
// Define input sequences
#define INPUT_LENGTH 12
#define INPUT_MIN 1
#define INPUT_MAX 5

#define ERR_INVALID_INPUT 999
// Flag that contains the number of the label reached, or negative if none
int ERR;

// Position of the input that triggered the error = length of the sequence
int ERR_POS;
// Array of inputs
int INPUTS[INPUT_LENGTH];

void __VERIFIER_error(int i) {
    fprintf(stderr, "error_%d ", i);
    ERR = i;
}

// Reinitialize automaton, see implementation below
void reset_eca();

// Reset flag
void reset_error() {
        ERR = -1;
}

void calculate_output(int);

// Process inputs
int loop()
{
    reset_error();
    reset_eca();
    // main i/o-loop
    for (int i = 0; i < INPUT_LENGTH; i++)
    {
        // read input
        int input = INPUTS[i];        
        // operate eca engine
        if((input != 2) && (input != 5) && (input != 3) && (input != 1) && (input != 4))
          return -2;
        calculate_output(input);
        if (ERR != -1) { 
                ERR_POS = i;
                return ERR;
        }
    }
    return -1;
}

// Calculate the next input sequence by incrementing the input at position pos
// with overflow. E.g. 1 1 1 19 -> 1 1 2 1 (if INPUT_MAX = 19)
void increment_inputs(int pos) {
        if (pos < 0) {
                fprintf(stderr, "Input overflow!\n");
                exit(1);
        }
        int newval = INPUTS[pos] + 1;
        if (newval > INPUT_MAX) {
                INPUTS[pos] = INPUT_MIN;
                increment_inputs(pos - 1);
        } else {
                INPUTS[pos] = newval;       
        }
}

// Reset all inputs to INPUT_MIN starting at position pos
void reset_inputs(int pos) {
        for (int i = pos; i < INPUT_LENGTH; i++) {
                INPUTS[i] = INPUT_MIN;
        }
}

void print_inputs() {
        fprintf(stderr, "%d: ", ERR_POS + 1);
        for (int i = 0; i <= ERR_POS; i++) {
                fprintf(stderr, "%d ", INPUTS[i]);
        }
        fprintf(stderr,"\n");
}

int main() {
        // Initialize input vector and calculate the max number of sequences 
        unsigned long long ninputs = 1;
        for (int i = 0; i < INPUT_LENGTH; ++i) {
                INPUTS[i] = INPUT_MIN;
                ninputs *= INPUT_MAX - INPUT_MIN + 1;
        }
        
        // Try input sequences
        for (long i = 0; i < ninputs; i++) {
                int result = loop();
                if (ERR >= 0) {
                        if (ERR != ERR_INVALID_INPUT) {
                                fprintf(stderr," -> ");
                                print_inputs();
                        }
                        // Skip all sequences with the same prefix
                        increment_inputs(ERR_POS);
                        reset_inputs(ERR_POS + 1);
                } else {                       
                        increment_inputs(INPUT_LENGTH - 1);
                }
        }
	return 0;
}

// Don't forget to:
// Make the implementation of reset_eca(), follow the pattern.
// Change all fprintf statements below this to stdout to separate the output
// Get rid of the old main() function, make sure to copy over the part where the 
// inputs are validated into the loop() function above
/////////////////////////////////////////////////////////////////////////////

	// inputs
	int inputs[] = {2,5,3,1,4};

	void errorCheck();
	void calculate_output(int);
	void calculate_outputm1(int);
	void calculate_outputm2(int);
	void calculate_outputm3(int);
	void calculate_outputm4(int);
	void calculate_outputm5(int);
	void calculate_outputm6(int);
	void calculate_outputm7(int);
	void calculate_outputm8(int);
	void calculate_outputm9(int);
	void calculate_outputm10(int);
	void calculate_outputm11(int);
	void calculate_outputm12(int);
	void calculate_outputm13(int);
	void calculate_outputm14(int);
	void calculate_outputm15(int);
	void calculate_outputm16(int);
	void calculate_outputm17(int);
	void calculate_outputm18(int);
	void calculate_outputm19(int);
	void calculate_outputm20(int);
	void calculate_outputm21(int);
	void calculate_outputm22(int);
	void calculate_outputm23(int);
	void calculate_outputm24(int);
	void calculate_outputm25(int);
	void calculate_outputm26(int);
	void calculate_outputm27(int);
	void calculate_outputm28(int);
	void calculate_outputm29(int);
	void calculate_outputm30(int);
	void calculate_outputm31(int);
	void calculate_outputm32(int);
	void calculate_outputm33(int);
	void calculate_outputm34(int);
	void calculate_outputm35(int);
	void calculate_outputm36(int);
	void calculate_outputm37(int);
	void calculate_outputm38(int);
	void calculate_outputm39(int);
	void calculate_outputm40(int);
	void calculate_outputm41(int);
	void calculate_outputm42(int);
	void calculate_outputm43(int);
	void calculate_outputm44(int);
	void calculate_outputm45(int);
	void calculate_outputm46(int);
	void calculate_outputm47(int);
	void calculate_outputm48(int);
	void calculate_outputm49(int);
	void calculate_outputm50(int);
	void calculate_outputm51(int);
	void calculate_outputm52(int);
	void calculate_outputm53(int);
	void calculate_outputm54(int);
	void calculate_outputm55(int);
	void calculate_outputm56(int);
	void calculate_outputm57(int);
	void calculate_outputm58(int);
	void calculate_outputm59(int);
	void calculate_outputm60(int);
	void calculate_outputm61(int);
	void calculate_outputm62(int);
	void calculate_outputm63(int);
	void calculate_outputm64(int);
	void calculate_outputm65(int);
	void calculate_outputm66(int);
	void calculate_outputm67(int);
	void calculate_outputm68(int);
	void calculate_outputm69(int);
	void calculate_outputm70(int);
	void calculate_outputm71(int);
	void calculate_outputm72(int);
	void calculate_outputm73(int);
	void calculate_outputm74(int);
	void calculate_outputm75(int);
	void calculate_outputm76(int);
	void calculate_outputm77(int);
	void calculate_outputm78(int);
	void calculate_outputm79(int);
	void calculate_outputm80(int);
	void calculate_outputm81(int);
	void calculate_outputm82(int);
	void calculate_outputm83(int);
	void calculate_outputm84(int);
	void calculate_outputm85(int);
	void calculate_outputm86(int);
	void calculate_outputm87(int);
	void calculate_outputm88(int);
	void calculate_outputm89(int);
	void calculate_outputm90(int);
	void calculate_outputm91(int);
	void calculate_outputm92(int);
	void calculate_outputm93(int);
	void calculate_outputm94(int);
	void calculate_outputm95(int);
	void calculate_outputm96(int);
	void calculate_outputm97(int);
	void calculate_outputm98(int);
	void calculate_outputm99(int);
	void calculate_outputm100(int);
	void calculate_outputm101(int);
	void calculate_outputm102(int);
	void calculate_outputm103(int);
	void calculate_outputm104(int);
	void calculate_outputm105(int);
	void calculate_outputm106(int);
	void calculate_outputm107(int);
	void calculate_outputm108(int);
	void calculate_outputm109(int);
	void calculate_outputm110(int);
	void calculate_outputm111(int);
	void calculate_outputm112(int);
	void calculate_outputm113(int);
	void calculate_outputm114(int);
	void calculate_outputm115(int);
	void calculate_outputm116(int);
	void calculate_outputm117(int);
	void calculate_outputm118(int);
	void calculate_outputm119(int);
	void calculate_outputm120(int);
	void calculate_outputm121(int);
	void calculate_outputm122(int);
	void calculate_outputm123(int);
	void calculate_outputm124(int);
	void calculate_outputm125(int);
	void calculate_outputm126(int);
	void calculate_outputm127(int);
	void calculate_outputm128(int);
	void calculate_outputm129(int);
	void calculate_outputm130(int);
	void calculate_outputm131(int);
	void calculate_outputm132(int);
	void calculate_outputm133(int);
	void calculate_outputm134(int);
	void calculate_outputm135(int);
	void calculate_outputm136(int);
	void calculate_outputm137(int);
	void calculate_outputm138(int);
	void calculate_outputm139(int);
	void calculate_outputm140(int);
	void calculate_outputm141(int);
	void calculate_outputm142(int);
	void calculate_outputm143(int);
	void calculate_outputm144(int);
	void calculate_outputm145(int);
	void calculate_outputm146(int);
	void calculate_outputm147(int);
	void calculate_outputm148(int);
	void calculate_outputm149(int);
	void calculate_outputm150(int);
	void calculate_outputm151(int);
	void calculate_outputm152(int);
	void calculate_outputm153(int);
	void calculate_outputm154(int);
	void calculate_outputm155(int);
	void calculate_outputm156(int);

	 int a7 = 5;
	 int a197  = 32;
	 int a92 = 5;
	 int a168 = 8;
	 int a67 = 10;
	 int a37 = 11;
	 int a109 = 6;
	 int a195 = 11;
	 int a79 = 9;
	 int a91 = 8;
	 int a111 = 10;
	 int a162  = 33;
	 int a63  = 32;
	 int a188 = 4;
	 int a56 = 10;
	 int a120  = 32;
	 int a170 = 6;
	 int a95 = 10;
	 int a110 = 10;
	 int a38  = 35;
	 int a39 = 2;
	 int a164  = 32;
	 int a155 = 13;
	 int a179 = 11;
	 int a14  = 32;
	 int a41 = 2;
	 int a44 = 9;
	 int a16  = 32;
	 int a60  = 32;
	 int a36 = 11;
	 int a191  = 32;
	 int a127  = 34;
	 int a6 = 11;
	 int a77 = 15;
	 int a160 = 9;
	 int a142 = 6;
	 int a90 = 6;
	 int a25  = 32;
	 int a23 = 4;
	 int a30  = 32;
	 int a104  = 36;
	 int cf = 1;
	 int a82 = 6;
	 int a69  = 34;
	 int a131  = 32;
	 int a15 = 11;
	 int a29  = 35;
	 int a65  = 34;
	 int a66  = 36;
	 int a189  = 34;
	 int a182 = 13;
	 int a117 = 17;
	 int a114 = 9;
	 int a24  = 32;
	 int a200  = 32;
	 int a154 = 11;
	 int a70  = 36;
	 int a0 = 11;
	 int a121 = 16;
	 int a31 = 3;
	 int a86  = 32;
	 int a196  = 32;
	 int a54 = 8;
	 int a129 = 14;
	 int a123  = 34;
	 int a150  = 32;
	 int a130 = 11;
	 int a176 = 7;
	 int a51  = 32;
	 int a116  = 33;
	 int a45 = 11;
	 int a84  = 34;
         
        void reset_eca() {
         a7 = 5;
	 a197  = 32;
	 a92 = 5;
	 a168 = 8;
	 a67 = 10;
	 a37 = 11;
	 a109 = 6;
	 a195 = 11;
	 a79 = 9;
	 a91 = 8;
	 a111 = 10;
	 a162  = 33;
	 a63  = 32;
	 a188 = 4;
	 a56 = 10;
	 a120  = 32;
	 a170 = 6;
	 a95 = 10;
	 a110 = 10;
	 a38  = 35;
	 a39 = 2;
	 a164  = 32;
	 a155 = 13;
	 a179 = 11;
	 a14  = 32;
	 a41 = 2;
	 a44 = 9;
	 a16  = 32;
	 a60  = 32;
	 a36 = 11;
	 a191  = 32;
	 a127  = 34;
	 a6 = 11;
	 a77 = 15;
	 a160 = 9;
	 a142 = 6;
	 a90 = 6;
	 a25  = 32;
	 a23 = 4;
	 a30  = 32;
	 a104  = 36;
	 cf = 1;
	 a82 = 6;
	 a69  = 34;
	 a131  = 32;
	 a15 = 11;
	 a29  = 35;
	 a65  = 34;
	 a66  = 36;
	 a189  = 34;
	 a182 = 13;
	 a117 = 17;
	 a114 = 9;
	 a24  = 32;
	 a200  = 32;
	 a154 = 11;
	 a70  = 36;
	 a0 = 11;
	 a121 = 16;
	 a31 = 3;
	 a86  = 32;
	 a196  = 32;
	 a54 = 8;
	 a129 = 14;
	 a123  = 34;
	 a150  = 32;
	 a130 = 11;
	 a176 = 7;
	 a51  = 32;
	 a116  = 33;
	 a45 = 11;
	 a84  = 34;
        }


	void errorCheck() {
	    if(((a90 == 9 && a160 == 8) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(0);
	    }
	    if(((a179 == 10 && a160 == 2) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(1);
	    }
	    if(((a91 == 6 && a69 == 32) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(2);
	    }
	    if(((a116 == 35 && a160 == 3) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(3);
	    }
	    if(((a110 == 12 && a109 == 7) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(4);
	    }
	    if(((a176 == 10 && a160 == 4) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(5);
	    }
	    if(((a179 == 12 && a60 == 36) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(6);
	    }
	    if(((a121 == 9 && a69 == 36) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(7);
	    }
	    if(((a45 == 13 && a109 == 2) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(8);
	    }
	    if(((a130 == 10 && a109 == 8) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(9);
	    }
	    if(((a67 == 8 && a69 == 34) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(10);
	    }
	    if(((a155 == 11 && a60 == 33) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(11);
	    }
	    if(((a155 == 13 && a60 == 33) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(12);
	    }
	    if(((a176 == 7 && a69 == 35) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(13);
	    }
	    if(((a31 == 4 && a104 == 32) && a56 == 13)){
	    cf = 0;
	    __VERIFIER_error(14);
	    }
	    if(((a29 == 32 && a160 == 4) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(15);
	    }
	    if(((a31 == 3 && a70 == 34) && a56 == 11)){
	    cf = 0;
	    __VERIFIER_error(16);
	    }
	    if(((a179 == 11 && a60 == 36) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(17);
	    }
	    if(((a31 == 6 && a104 == 32) && a56 == 13)){
	    cf = 0;
	    __VERIFIER_error(18);
	    }
	    if(((a195 == 8 && a104 == 34) && a56 == 13)){
	    cf = 0;
	    __VERIFIER_error(19);
	    }
	    if(((a160 == 4 && a109 == 3) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(20);
	    }
	    if(((a154 == 7 && a38 == 33) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(21);
	    }
	    if(((a110 == 8 && a109 == 7) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(22);
	    }
	    if(((a90 == 5 && a160 == 8) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(23);
	    }
	    if(((a189 == 36 && a70 == 33) && a56 == 11)){
	    cf = 0;
	    __VERIFIER_error(24);
	    }
	    if(((a31 == 4 && a70 == 34) && a56 == 11)){
	    cf = 0;
	    __VERIFIER_error(25);
	    }
	    if(((a162 == 36 && a104 == 33) && a56 == 13)){
	    cf = 0;
	    __VERIFIER_error(26);
	    }
	    if(((a155 == 7 && a60 == 33) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(27);
	    }
	    if(((a182 == 12 && a60 == 34) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(28);
	    }
	    if(((a45 == 16 && a109 == 2) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(29);
	    }
	    if(((a110 == 11 && a109 == 7) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(30);
	    }
	    if(((a69 == 35 && a160 == 9) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(31);
	    }
	    if(((a65 == 33 && a109 == 4) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(32);
	    }
	    if(((a110 == 10 && a109 == 7) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(33);
	    }
	    if(((a51 == 34 && a109 == 6) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(34);
	    }
	    if(((a160 == 5 && a109 == 3) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(35);
	    }
	    if(((a90 == 11 && a160 == 7) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(36);
	    }
	    if(((a179 == 16 && a60 == 36) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(37);
	    }
	    if(((a123 == 36 && a160 == 5) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(38);
	    }
	    if(((a130 == 12 && a109 == 8) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(39);
	    }
	    if(((a90 == 10 && a160 == 7) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(40);
	    }
	    if(((a176 == 6 && a160 == 4) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(41);
	    }
	    if(((a129 == 15 && a160 == 6) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(42);
	    }
	    if(((a23 == 7 && a69 == 33) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(43);
	    }
	    if(((a130 == 15 && a109 == 8) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(44);
	    }
	    if(((a116 == 32 && a160 == 3) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(45);
	    }
	    if(((a45 == 14 && a109 == 2) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(46);
	    }
	    if(((a66 == 33 && a60 == 32) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(47);
	    }
	    if(((a182 == 15 && a60 == 34) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(48);
	    }
	    if(((a117 == 17 && a38 == 36) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(49);
	    }
	    if(((a66 == 34 && a60 == 32) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(50);
	    }
	    if(((a23 == 2 && a160 == 9) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(51);
	    }
	    if(((a189 == 32 && a70 == 33) && a56 == 11)){
	    cf = 0;
	    __VERIFIER_error(52);
	    }
	    if(((a67 == 10 && a69 == 34) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(53);
	    }
	    if(((a182 == 10 && a60 == 34) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(54);
	    }
	    if(((a179 == 13 && a160 == 2) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(55);
	    }
	    if(((a65 == 32 && a109 == 4) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(56);
	    }
	    if(((a179 == 14 && a60 == 36) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(57);
	    }
	    if(((a176 == 8 && a69 == 35) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(58);
	    }
	    if(((a127 == 33 && a38 == 35) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(59);
	    }
	    if(((a176 == 3 && a69 == 35) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(60);
	    }
	    if(((a176 == 10 && a69 == 35) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(61);
	    }
	    if(((a44 == 9 && a160 == 7) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(62);
	    }
	    if(((a23 == 4 && a109 == 9) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(63);
	    }
	    if(((a154 == 8 && a38 == 33) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(64);
	    }
	    if(((a54 == 5 && a160 == 8) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(65);
	    }
	    if(((a6 == 6 && a38 == 34) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(66);
	    }
	    if(((a69 == 33 && a160 == 9) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(67);
	    }
	    if(((a121 == 16 && a69 == 36) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(68);
	    }
	    if(((a176 == 6 && a69 == 35) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(69);
	    }
	    if(((a77 == 8 && a60 == 35) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(70);
	    }
	    if(((a130 == 17 && a160 == 3) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(71);
	    }
	    if(((a176 == 5 && a160 == 4) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(72);
	    }
	    if(((a176 == 4 && a160 == 4) && a56 == 10)){
	    cf = 0;
	    __VERIFIER_error(73);
	    }
	    if(((a36 == 11 && a160 == 2) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(74);
	    }
	    if(((a77 == 14 && a60 == 35) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(75);
	    }
	    if(((a31 == 8 && a104 == 32) && a56 == 13)){
	    cf = 0;
	    __VERIFIER_error(76);
	    }
	    if(((a65 == 36 && a109 == 4) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(77);
	    }
	    if(((a129 == 14 && a160 == 6) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(78);
	    }
	    if(((a36 == 7 && a160 == 2) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(79);
	    }
	    if(((a23 == 6 && a109 == 9) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(80);
	    }
	    if(((a67 == 13 && a69 == 34) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(81);
	    }
	    if(((a29 == 34 && a160 == 4) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(82);
	    }
	    if(((a130 == 15 && a160 == 3) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(83);
	    }
	    if(((a69 == 34 && a160 == 9) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(84);
	    }
	    if(((a6 == 7 && a38 == 34) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(85);
	    }
	    if(((a44 == 6 && a160 == 7) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(86);
	    }
	    if(((a6 == 8 && a38 == 34) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(87);
	    }
	    if(((a6 == 11 && a38 == 34) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(88);
	    }
	    if(((a44 == 10 && a160 == 7) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(89);
	    }
	    if(((a114 == 12 && a38 == 32) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(90);
	    }
	    if(((a162 == 32 && a104 == 33) && a56 == 13)){
	    cf = 0;
	    __VERIFIER_error(91);
	    }
	    if(((a67 == 15 && a69 == 34) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(92);
	    }
	    if(((a67 == 11 && a69 == 34) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(93);
	    }
	    if(((a84 == 34 && a109 == 5) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(94);
	    }
	    if(((a182 == 17 && a60 == 34) && a56 == 9)){
	    cf = 0;
	    __VERIFIER_error(95);
	    }
	    if(((a23 == 2 && a69 == 33) && a56 == 7)){
	    cf = 0;
	    __VERIFIER_error(96);
	    }
	    if(((a54 == 8 && a160 == 8) && a56 == 8)){
	    cf = 0;
	    __VERIFIER_error(97);
	    }
	    if(((a154 == 6 && a38 == 33) && a56 == 14)){
	    cf = 0;
	    __VERIFIER_error(98);
	    }
	    if(((a160 == 7 && a109 == 3) && a56 == 12)){
	    cf = 0;
	    __VERIFIER_error(99);
	    }
	}
 void calculate_outputm46(int input) {
    if(((a168 == 7 && ((((input == 4) &&  cf==1 ) && a92 == 4) && a63 == 33)) && (a0 == 10 && (a164 == 33 && a41 == 1)))) {
    	cf = 0;
    	a56 = 12;
    	a82 = 6;
    	a14 = 32 ;
    	a95 = 10;
    	a188 = 5;
    	a39 = 2;
    	a168 = 8;
    	a25 = 32 ;
    	a164 = 32 ;
    	a24 = 34 ;
    	a79 = 9;
    	a111 = 10;
    	a109 = 7;
    	a191 = 32 ;
    	a196 = 32 ;
    	a150 = 32 ;
    	a131 = 33 ;
    	a200 = 32 ;
    	a37 = 11;
    	a7 = 5;
    	a41 = 2;
    	a92 = 5;
    	a63 = 32 ;
    	a0 = 11;
    	a197 = 34 ;
    	a110 = 13; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a191 == 33 && a7 == 4) && (a111 == 9 && (((a86 == 33 && ((input == 2) &&  cf==1 )) && a14 == 33) && a15 == 10)))) {
    	cf = 0;
    	a56 = 11;
    	a150 = 32 ;
    	a7 = 5;
    	a86 = 32 ;
    	a14 = 32 ;
    	a70 = 34 ;
    	a164 = 32 ;
    	a95 = 10;
    	a197 = 32 ;
    	a31 = 3; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a15 == 10 && (a41 == 1 && (((input == 5) &&  cf==1 ) && a37 == 10))) && (a111 == 9 && (a41 == 1 && a25 == 33)))) {
    	cf = 0;
    	a14 = 32 ;
    	a189 = 36 ;
    	a86 = 32 ;
    	a79 = 9;
    	a164 = 32 ;
    	a39 = 2;
    	a191 = 32 ;
    	a63 = 32 ;
    	a150 = 32 ;
    	a92 = 5;
    	a7 = 5;
    	a197 = 32 ;
    	a70 = 33 ;
    	a56 = 11; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a7 == 4 && (((input == 1) &&  cf==1 ) && a197 == 33)) && (a24 == 33 && (a25 == 33 && (a82 == 5 && a200 == 33))))) {
    	cf = 0;
    	a69 = 34 ;
    	a131 = 33 ;
    	a120 = 33 ;
    	a67 = 10; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a95 == 9 && a39 == 1) && (a82 == 5 && (((( cf==1  && (input == 3)) && a15 == 10) && a150 == 33) && a150 == 33)))) {
    	cf = 0;
    	a39 = 2;
    	a24 = 32 ;
    	a41 = 2;
    	a168 = 8;
    	a82 = 6;
    	a63 = 32 ;
    	a56 = 14;
    	a38 = 33 ;
    	a95 = 10;
    	a7 = 5;
    	a79 = 9;
    	a154 = 6; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm2(int input) {
    if((((a200 == 33 && (a91 == 10 &&  cf==1 )) && a197 == 33) && ((a41 == 1 && (a95 == 9 && a24 == 33)) && a150 == 33))) {
    	calculate_outputm46(input);
    } 
}
 void calculate_outputm60(int input) {
    if(((a120 == 32 && (a168 == 8 && (a15 == 11 && a111 == 10))) && (a82 == 6 && (( cf==1  && (input == 4)) && a92 == 5)))) {
    	cf = 0;
    	a160 = 6;
    	a129 = 14; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a25 == 32 && (a191 == 32 && (a41 == 2 && (((input == 5) &&  cf==1 ) && a150 == 32)))) && (a92 == 5 && a111 == 10))) {
    	cf = 0;
    	a56 = 10;
    	a86 = 34 ;
    	a160 = 4;
    	a176 = 9; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((((input == 2) &&  cf==1 ) && a196 == 32) && ((a7 == 5 && (a37 == 11 && (a0 == 11 && a197 == 32))) && a188 == 4))) {
    	cf = 0;
    	a109 = 7;
    	a56 = 12;
    	a110 = 11; 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((( cf==1  && (input == 3)) && a150 == 32) && a63 == 32) && (a170 == 6 && ((a120 == 32 && a39 == 2) && a111 == 10)))) {
    	cf = 0;
    	a160 = 7;
    	a44 = 6; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((a200 == 32 && (( cf==1  && (input == 1)) && a142 == 6)) && a196 == 32) && (a86 == 32 && (a196 == 32 && a86 == 32)))) {
    	cf = 0;
    	a38 = 32 ;
    	a56 = 14;
    	a114 = 12; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm6(int input) {
    if(((a197 == 32 && a24 == 32) && (a131 == 32 && ((a41 == 2 && (a92 == 5 && (a36 == 10 &&  cf==1 ))) && a30 == 32)))) {
    	calculate_outputm60(input);
    } 
}
 void calculate_outputm67(int input) {
    if(((a170 == 6 && ((a37 == 11 && a7 == 5) && a7 == 5)) && ((a95 == 10 && ( cf==1  && (input == 3))) && a39 == 2))) {
    	cf = 0;
    	a92 = 5;
    	a129 = 12; 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((a7 == 5 && a191 == 32) && a39 == 2) && (a95 == 10 && ((((input == 5) &&  cf==1 ) && a188 == 4) && a164 == 32)))) {
    	cf = 0;
    	a25 = 34 ;
    	a188 = 5;
    	a111 = 11;
    	a95 = 11;
    	a150 = 34 ;
    	a142 = 7;
    	a60 = 35 ;
    	a37 = 12;
    	a56 = 9;
    	a170 = 7;
    	a196 = 34 ;
    	a41 = 3;
    	a63 = 34 ;
    	a7 = 6;
    	a24 = 34 ;
    	a0 = 12;
    	a200 = 34 ;
    	a16 = 34 ;
    	a77 = 14; 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((a196 == 32 && ((a170 == 6 && (a0 == 11 && a200 == 32)) && a82 == 6)) && a120 == 32) && ((input == 2) &&  cf==1 ))) {
    	cf = 0;
    	a129 = 15; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a196 == 32 && a111 == 10) && (a0 == 11 && (a150 == 32 && ((a30 == 32 && ( cf==1  && (input == 1))) && a82 == 6))))) {
    	cf = 0;
    	a170 = 5;
    	a0 = 10;
    	a63 = 33 ;
    	a86 = 33 ;
    	a24 = 33 ;
    	a191 = 33 ;
    	a69 = 33 ;
    	a200 = 33 ;
    	a79 = 8;
    	a168 = 7;
    	a197 = 33 ;
    	a56 = 7;
    	a39 = 1;
    	a188 = 3;
    	a150 = 33 ;
    	a7 = 4;
    	a23 = 7; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a196 == 32 && (( cf==1  && (input == 4)) && a41 == 2)) && (((a86 == 32 && a111 == 10) && a24 == 32) && a164 == 32))) {
    	cf = 0;
    	a56 = 12;
    	a109 = 3;
    	a160 = 5; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm68(int input) {
    if(((((a41 == 2 && a200 == 32) && a41 == 2) && a164 == 32) && ((a63 == 32 && ( cf==1  && (input == 2))) && a63 == 32))) {
    	cf = 0;
    	a160 = 2;
    	a56 = 10;
    	a179 = 13; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((a142 == 6 && (((input == 4) &&  cf==1 ) && a39 == 2)) && a168 == 8) && (a0 == 11 && (a131 == 32 && a63 == 32)))) {
    	cf = 0;
    	a131 = 32 ;
    	a160 = 7;
    	a63 = 32 ;
    	a44 = 4; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a95 == 10 && ((a92 == 5 && a150 == 32) && a15 == 11)) && (a92 == 5 && (a131 == 32 && ( cf==1  && (input == 5)))))) {
    	cf = 0;
    	a109 = 3;
    	a56 = 12;
    	a160 = 7; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((a131 == 32 && a95 == 10) && a82 == 6) && (a79 == 9 && (a7 == 5 && (a191 == 32 && ((input == 1) &&  cf==1 )))))) {
    	cf = 0;
    	a162 = 36 ;
    	a104 = 33 ;
    	a56 = 13; 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((a150 == 32 && (a197 == 32 && a7 == 5)) && a39 == 2) && ((a131 == 32 && ((input == 3) &&  cf==1 )) && a164 == 32))) {
    	cf = 0;
    	a164 = 34 ;
    	a86 = 34 ;
    	a95 = 11;
    	a41 = 3;
    	a7 = 6;
    	a63 = 34 ;
    	a196 = 34 ;
    	a56 = 9;
    	a197 = 34 ;
    	a170 = 7;
    	a39 = 3;
    	a168 = 9;
    	a30 = 34 ;
    	a191 = 34 ;
    	a142 = 7;
    	a111 = 11;
    	a92 = 6;
    	a16 = 34 ;
    	a15 = 12;
    	a200 = 34 ;
    	a60 = 35 ;
    	a14 = 34 ;
    	a150 = 34 ;
    	a82 = 7;
    	a0 = 12;
    	a24 = 34 ;
    	a120 = 34 ;
    	a25 = 34 ;
    	a77 = 13; 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
}
 void calculate_outputm10(int input) {
    if(((a25 == 32 && (a129 == 11 &&  cf==1 )) && ((a111 == 10 && ((a191 == 32 && a79 == 9) && a79 == 9)) && a111 == 10))) {
    	calculate_outputm67(input);
    } 
    if((((a63 == 32 && (a142 == 6 && a131 == 32)) && a95 == 10) && (a7 == 5 && ((a129 == 12 &&  cf==1 ) && a188 == 4)))) {
    	calculate_outputm68(input);
    } 
}
 void calculate_outputm71(int input) {
    if(((a111 == 10 && (a170 == 6 && a188 == 4)) && (((( cf==1  && (input == 4)) && a30 == 32) && a164 == 32) && a120 == 32))) {
    	cf = 0;
    	a92 = 6;
    	a160 = 6;
    	a129 = 11; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((( cf==1  && (input == 1)) && a0 == 11) && ((((a39 == 2 && a82 == 6) && a164 == 32) && a168 == 8) && a37 == 11))) {
    	cf = 0;
    	a123 = 36 ;
    	a160 = 5; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a14 == 32 && (a196 == 32 && a41 == 2)) && ((a79 == 9 && (((input == 3) &&  cf==1 ) && a15 == 11)) && a188 == 4))) {
    	cf = 0;
    	a92 = 6;
    	a160 = 6;
    	a129 = 11; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((a200 == 32 && ( cf==1  && (input == 5))) && a95 == 10) && (((a37 == 11 && a95 == 10) && a25 == 32) && a120 == 32))) {
    	cf = 0;
    	a160 = 6;
    	a92 = 6;
    	a129 = 11; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((((( cf==1  && (input == 2)) && a25 == 32) && a142 == 6) && a168 == 8) && (a197 == 32 && (a200 == 32 && a14 == 32)))) {
    	cf = 0;
    	a104 = 33 ;
    	a162 = 32 ;
    	a56 = 13; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm11(int input) {
    if((((( cf==1  && a44 == 4) && a14 == 32) && a25 == 32) && ((a7 == 5 && (a92 == 5 && a7 == 5)) && a16 == 32))) {
    	calculate_outputm71(input);
    } 
}
 void calculate_outputm90(int input) {
    if(((a15 == 12 && (a41 == 3 && (a111 == 11 && a24 == 34))) && ((( cf==1  && (input == 2)) && a30 == 34) && a86 == 34))) {
    	cf = 0;
    	a60 = 36 ;
    	a179 = 16; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a14 == 34 && ((( cf==1  && (input == 4)) && a41 == 3) && a30 == 34)) && (a196 == 34 && (a142 == 7 && a142 == 7)))) {
    	cf = 0;
    	a168 = 7;
    	a37 = 12;
    	a188 = 5;
    	a79 = 8;
    	a131 = 34 ;
    	a60 = 36 ;
    	a179 = 13; 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if(((a16 == 34 && a0 == 12) && (a150 == 34 && ((a63 == 34 && (a168 == 9 && ( cf==1  && (input == 1)))) && a95 == 11)))) {
    	cf = 0;
    	a56 = 8;
    	a14 = 32 ;
    	a150 = 32 ;
    	a16 = 32 ;
    	a30 = 32 ;
    	a86 = 32 ;
    	a63 = 32 ;
    	a25 = 32 ;
    	a7 = 5;
    	a170 = 6;
    	a41 = 2;
    	a69 = 35 ;
    	a95 = 10;
    	a142 = 6;
    	a160 = 9; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((a16 == 34 && (((input == 3) &&  cf==1 ) && a95 == 11)) && a197 == 34) && (a164 == 34 && (a170 == 7 && a39 == 3)))) {
    	cf = 0;
    	a25 = 32 ;
    	a86 = 32 ;
    	a197 = 32 ;
    	a150 = 32 ;
    	a30 = 32 ;
    	a70 = 33 ;
    	a164 = 32 ;
    	a14 = 32 ;
    	a7 = 5;
    	a200 = 32 ;
    	a170 = 6;
    	a189 = 32 ;
    	a39 = 2;
    	a56 = 11; 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((a25 == 34 && (a15 == 12 && a164 == 34)) && (a200 == 34 && (a191 == 34 && (a142 == 7 && ((input == 5) &&  cf==1 )))))) {
    	cf = 0;
    	a30 = 32 ;
    	a7 = 5;
    	a14 = 32 ;
    	a150 = 32 ;
    	a200 = 32 ;
    	a63 = 32 ;
    	a191 = 32 ;
    	a56 = 11;
    	a164 = 32 ;
    	a86 = 32 ;
    	a197 = 32 ;
    	a70 = 34 ;
    	a31 = 4; 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
}
 void calculate_outputm17(int input) {
    if(((a25 == 34 && (a164 == 34 && (a150 == 34 && (( cf==1  && a77 == 13) && a63 == 34)))) && (a170 == 7 && a15 == 12))) {
    	calculate_outputm90(input);
    } 
}
 void calculate_outputm94(int input) {
    if(((a7 == 6 && (a196 == 34 && ((((input == 3) &&  cf==1 ) && a197 == 34) && a7 == 6))) && (a86 == 34 && a30 == 34))) {
    	cf = 0;
    	a15 = 10;
    	a39 = 1;
    	a7 = 4;
    	a197 = 33 ;
    	a63 = 33 ;
    	a95 = 9;
    	a120 = 33 ;
    	a150 = 33 ;
    	a86 = 33 ;
    	a0 = 10;
    	a56 = 7;
    	a69 = 35 ;
    	a82 = 5;
    	a176 = 10; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a95 == 11 && (a82 == 7 && (a142 == 7 && a82 == 7))) && ((a95 == 11 && ((input == 5) &&  cf==1 )) && a95 == 11))) {
    	cf = 0;
    	a7 = 5;
    	a82 = 6;
    	a111 = 10;
    	a86 = 32 ;
    	a196 = 32 ;
    	a56 = 8;
    	a188 = 4;
    	a142 = 6;
    	a160 = 8;
    	a24 = 32 ;
    	a25 = 32 ;
    	a39 = 2;
    	a150 = 32 ;
    	a79 = 9;
    	a164 = 32 ;
    	a54 = 8; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((((a191 == 34 && ((input == 1) &&  cf==1 )) && a150 == 34) && a86 == 34) && (a92 == 6 && (a120 == 34 && a39 == 3)))) {
    	cf = 0;
    	a16 = 32 ;
    	a168 = 8;
    	a191 = 32 ;
    	a150 = 32 ;
    	a170 = 6;
    	a95 = 10;
    	a0 = 11;
    	a197 = 32 ;
    	a120 = 32 ;
    	a24 = 32 ;
    	a7 = 5;
    	a39 = 2;
    	a200 = 32 ;
    	a14 = 32 ;
    	a86 = 32 ;
    	a15 = 11;
    	a41 = 2;
    	a160 = 7;
    	a56 = 8;
    	a142 = 6;
    	a131 = 32 ;
    	a25 = 32 ;
    	a63 = 32 ;
    	a79 = 9;
    	a196 = 32 ;
    	a164 = 32 ;
    	a30 = 32 ;
    	a188 = 4;
    	a82 = 6;
    	a37 = 11;
    	a92 = 5;
    	a111 = 10;
    	a44 = 4; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a188 == 5 && (a25 == 34 && a37 == 12)) && (a16 == 34 && ((a200 == 34 && ((input == 2) &&  cf==1 )) && a82 == 7)))) {
    	cf = 0;
    	a150 = 33 ;
    	a69 = 34 ;
    	a0 = 10;
    	a24 = 33 ;
    	a86 = 33 ;
    	a197 = 33 ;
    	a7 = 4;
    	a15 = 10;
    	a37 = 10;
    	a120 = 33 ;
    	a131 = 33 ;
    	a63 = 33 ;
    	a95 = 9;
    	a56 = 7;
    	a67 = 11; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((a25 == 34 && a197 == 34) && a15 == 12) && (a0 == 12 && (a131 == 34 && (( cf==1  && (input == 4)) && a14 == 34))))) {
    	cf = 0;
    	a188 = 4;
    	a30 = 32 ;
    	a164 = 32 ;
    	a95 = 10;
    	a142 = 6;
    	a170 = 6;
    	a25 = 32 ;
    	a92 = 5;
    	a120 = 32 ;
    	a16 = 32 ;
    	a79 = 9;
    	a39 = 2;
    	a24 = 32 ;
    	a111 = 10;
    	a7 = 5;
    	a82 = 6;
    	a150 = 32 ;
    	a15 = 11;
    	a41 = 2;
    	a86 = 32 ;
    	a14 = 32 ;
    	a191 = 32 ;
    	a168 = 8;
    	a63 = 32 ;
    	a160 = 7;
    	a197 = 32 ;
    	a196 = 32 ;
    	a200 = 32 ;
    	a0 = 11;
    	a131 = 32 ;
    	a56 = 8;
    	a37 = 11;
    	a44 = 4; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm18(int input) {
    if(((( cf==1  && a179 == 13) && a188 == 5) && ((((a16 == 34 && a111 == 11) && a170 == 7) && a14 == 34) && a37 == 12))) {
    	calculate_outputm94(input);
    } 
}
 void calculate_outputm99(int input) {
    if((((((a92 == 5 && a37 == 11) && a142 == 6) && a168 == 8) && a41 == 2) && (a170 == 6 && ( cf==1  && (input == 3))))) {
    	cf = 0;
    	a109 = 8;
    	a56 = 12;
    	a197 = 34 ;
    	a39 = 2;
    	a164 = 33 ;
    	a130 = 13; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((((input == 2) &&  cf==1 ) && a200 == 32) && (a7 == 5 && (a188 == 4 && ((a168 == 8 && a142 == 6) && a15 == 11))))) {
    	cf = 0;
    	a109 = 8;
    	a56 = 12;
    	a130 = 12; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a168 == 8 && a197 == 32) && (a120 == 32 && (((( cf==1  && (input == 5)) && a196 == 32) && a92 == 5) && a41 == 2)))) {
    	cf = 0;
    	a60 = 34 ;
    	a82 = 7;
    	a15 = 12;
    	a7 = 6;
    	a200 = 34 ;
    	a24 = 34 ;
    	a41 = 3;
    	a188 = 5;
    	a56 = 9;
    	a197 = 34 ;
    	a111 = 11;
    	a120 = 34 ;
    	a150 = 34 ;
    	a16 = 34 ;
    	a170 = 7;
    	a25 = 34 ;
    	a37 = 12;
    	a191 = 34 ;
    	a182 = 17; 
    	 printf("%d\n", 19); fflush(stdout); 
    } 
    if((((a16 == 32 && (a79 == 9 && a30 == 32)) && a37 == 11) && ((a164 == 32 && ( cf==1  && (input == 1))) && a37 == 11))) {
    	cf = 0;
    	a29 = 32 ;
    	a56 = 8;
    	a160 = 4; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a95 == 10 && a120 == 32) && (a30 == 32 && (a41 == 2 && ((a111 == 10 && ((input == 4) &&  cf==1 )) && a170 == 6))))) {
    	cf = 0;
    	a56 = 12;
    	a65 = 36 ;
    	a109 = 4; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm20(int input) {
    if(((a200 == 32 && (a92 == 5 && a7 == 5)) && (a200 == 32 && (((a116 == 33 &&  cf==1 ) && a142 == 6) && a79 == 9)))) {
    	calculate_outputm99(input);
    } 
}
 void calculate_outputm105(int input) {
    if(((a164 == 32 && (a150 == 32 && (a0 == 11 && a170 == 6))) && (a30 == 32 && (( cf==1  && (input == 5)) && a191 == 32)))) {
    	cf = 0;
    	a109 = 9;
    	a56 = 12;
    	a23 = 6; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((a92 == 5 && a168 == 8) && a39 == 2) && (((a168 == 8 && ((input == 2) &&  cf==1 )) && a37 == 11) && a200 == 32))) {
    	cf = 0;
    	a41 = 3;
    	a37 = 12;
    	a79 = 10;
    	a25 = 34 ;
    	a168 = 9;
    	a111 = 11;
    	a150 = 34 ;
    	a200 = 34 ;
    	a142 = 7;
    	a196 = 34 ;
    	a188 = 5;
    	a16 = 34 ;
    	a60 = 32 ;
    	a24 = 34 ;
    	a66 = 34 ;
    	a56 = 9; 
    	 printf("%d\n", 19); fflush(stdout); 
    } 
    if(((a25 == 32 && (a95 == 10 && ( cf==1  && (input == 4)))) && (a131 == 32 && ((a63 == 32 && a92 == 5) && a30 == 32)))) {
    	cf = 0;
    	a86 = 33 ;
    	a0 = 10;
    	a56 = 7;
    	a200 = 33 ;
    	a79 = 8;
    	a37 = 10;
    	a63 = 33 ;
    	a69 = 33 ;
    	a24 = 33 ;
    	a150 = 33 ;
    	a197 = 33 ;
    	a188 = 3;
    	a170 = 5;
    	a7 = 4;
    	a111 = 9;
    	a23 = 2; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((( cf==1  && (input == 1)) && a0 == 11) && ((a120 == 32 && ((a82 == 6 && a168 == 8) && a196 == 32)) && a170 == 6))) {
    	cf = 0;
    	a56 = 8;
    	a86 = 32 ;
    	a160 = 7;
    	a44 = 10; 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((a14 == 32 && (((( cf==1  && (input == 3)) && a170 == 6) && a196 == 32) && a120 == 32)) && (a164 == 32 && a120 == 32))) {
    	cf = 0;
    	a116 = 33 ;
    	a39 = 3;
    	a86 = 32 ;
    	a160 = 3; 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
}
 void calculate_outputm21(int input) {
    if((((a168 == 8 && (a176 == 9 &&  cf==1 )) && a111 == 10) && ((a41 == 2 && (a191 == 32 && a200 == 32)) && a188 == 4))) {
    	calculate_outputm105(input);
    } 
}
 void calculate_outputm111(int input) {
    if(((((a79 == 9 && a25 == 32) && a197 == 32) && a30 == 32) && ((a41 == 2 && ((input == 1) &&  cf==1 )) && a200 == 32))) {
    	cf = 0;
    	a92 = 6;
    	a160 = 6;
    	a56 = 8;
    	a129 = 11; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((( cf==1  && (input == 5)) && a95 == 10) && a0 == 11) && ((a120 == 32 && (a63 == 32 && a41 == 2)) && a15 == 11))) {
    	cf = 0;
    	a109 = 3;
    	a56 = 12;
    	a160 = 4; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((a25 == 32 && ( cf==1  && (input == 4))) && a168 == 8) && (a95 == 10 && ((a164 == 32 && a16 == 32) && a92 == 5)))) {
    	cf = 0;
    	a109 = 2;
    	a56 = 12;
    	a45 = 16; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm113(int input) {
    if((((((input == 4) &&  cf==1 ) && a131 == 32) && a197 == 32) && ((a39 == 2 && (a24 == 32 && a142 == 6)) && a188 == 4))) {
    	cf = 0;
    	a23 = 1; 
    	 printf("%d\n", 19); fflush(stdout); 
    } 
    if(((a0 == 11 && ((a16 == 32 && (a111 == 10 && ( cf==1  && (input == 2)))) && a24 == 32)) && (a131 == 32 && a63 == 32))) {
    	cf = 0;
    	a86 = 34 ;
    	a160 = 4;
    	a176 = 9; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm24(int input) {
    if(((a168 == 8 && (a170 == 6 && (a39 == 2 && a16 == 32))) && ((a39 == 2 && (a23 == 1 &&  cf==1 )) && a196 == 32))) {
    	calculate_outputm111(input);
    } 
    if((((((a14 == 32 && ( cf==1  && a23 == 4)) && a30 == 32) && a150 == 32) && a41 == 2) && (a79 == 9 && a25 == 32))) {
    	calculate_outputm113(input);
    } 
}
 void calculate_outputm126(int input) {
    if((((a92 == 5 && a131 == 32) && a131 == 32) && ((a82 == 6 && (( cf==1  && (input == 3)) && a41 == 2)) && a111 == 10))) {
    	cf = 0;
    	a56 = 14;
    	a38 = 34 ;
    	a6 = 8; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((a95 == 10 && a30 == 32) && a63 == 32) && (a37 == 11 && ((a150 == 32 && ((input == 2) &&  cf==1 )) && a168 == 8)))) {
    	cf = 0;
    	a84 = 34 ;
    	a109 = 5; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a131 == 32 && ( cf==1  && (input == 1))) && (a41 == 2 && (a30 == 32 && (a170 == 6 && (a16 == 32 && a120 == 32)))))) {
    	cf = 0;
    	a56 = 14;
    	a38 = 34 ;
    	a6 = 11; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a41 == 2 && (a170 == 6 && (((( cf==1  && (input == 5)) && a82 == 6) && a191 == 32) && a39 == 2))) && a95 == 10)) {
    	cf = 0;
    	a56 = 10;
    	a86 = 34 ;
    	a160 = 4;
    	a176 = 9; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a14 == 32 && (a150 == 32 && a15 == 11)) && (a15 == 11 && ((a111 == 10 && ( cf==1  && (input == 4))) && a79 == 9)))) {
    	cf = 0;
    	a160 = 8;
    	a56 = 8;
    	a54 = 5; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm29(int input) {
    if(((((a150 == 32 && (( cf==1  && a65 == 34) && a197 == 32)) && a120 == 32) && a79 == 9) && (a30 == 32 && a92 == 5))) {
    	calculate_outputm126(input);
    } 
}
 void calculate_outputm134(int input) {
    if((( cf==1  && (input == 5)) && (a200 == 32 && (a7 == 5 && (a37 == 11 && (a150 == 32 && (a7 == 5 && a191 == 32))))))) {
    	cf = 0;
    	a95 = 11;
    	a39 = 3;
    	a191 = 34 ;
    	a60 = 34 ;
    	a82 = 7;
    	a0 = 12;
    	a111 = 11;
    	a25 = 34 ;
    	a41 = 3;
    	a56 = 9;
    	a200 = 34 ;
    	a16 = 34 ;
    	a182 = 12; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((((a25 == 32 && a191 == 32) && a200 == 32) && a0 == 11) && (a79 == 9 && (a82 == 6 && ((input == 3) &&  cf==1 ))))) {
    	cf = 0;
    	a15 = 11;
    	a188 = 4;
    	a131 = 32 ;
    	a86 = 32 ;
    	a197 = 32 ;
    	a200 = 32 ;
    	a24 = 32 ;
    	a65 = 34 ;
    	a109 = 4; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a39 == 2 && a0 == 11) && (a16 == 32 && (a200 == 32 && ((a170 == 6 && ( cf==1  && (input == 1))) && a25 == 32))))) {
    	cf = 0;
    	a200 = 33 ;
    	a197 = 33 ;
    	a150 = 33 ;
    	a0 = 10;
    	a63 = 33 ;
    	a168 = 7;
    	a7 = 4;
    	a120 = 33 ;
    	a191 = 33 ;
    	a39 = 1;
    	a196 = 33 ;
    	a56 = 7;
    	a69 = 35 ;
    	a176 = 8; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((a168 == 8 && a16 == 32) && a170 == 6) && (a25 == 32 && (a196 == 32 && (a30 == 32 && ( cf==1  && (input == 4))))))) {
    	cf = 0;
    	a56 = 8;
    	a197 = 32 ;
    	a86 = 32 ;
    	a188 = 4;
    	a131 = 32 ;
    	a15 = 11;
    	a160 = 2;
    	a24 = 32 ;
    	a36 = 10; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a191 == 32 && (a39 == 2 && ((input == 2) &&  cf==1 ))) && ((a79 == 9 && (a63 == 32 && a111 == 10)) && a150 == 32))) {
    	cf = 0;
    	a56 = 8;
    	a86 = 32 ;
    	a188 = 4;
    	a197 = 32 ;
    	a160 = 7;
    	a44 = 9; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm32(int input) {
    if((((a111 == 10 && ( cf==1  && a110 == 13)) && a168 == 8) && (((a164 == 32 && a41 == 2) && a79 == 9) && a142 == 6))) {
    	calculate_outputm134(input);
    } 
}
 void calculate_outputm137(int input) {
    if((((a170 == 6 && a168 == 8) && a25 == 32) && ((a92 == 5 && (a150 == 32 && ((input == 4) &&  cf==1 ))) && a63 == 32))) {
    	cf = 0;
    	a56 = 13;
    	a104 = 32 ;
    	a31 = 4; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a92 == 5 && (a24 == 32 && a41 == 2)) && (a150 == 32 && (a191 == 32 && (((input == 3) &&  cf==1 ) && a15 == 11))))) {
    	cf = 0;
    	a104 = 32 ;
    	a197 = 32 ;
    	a56 = 13;
    	a31 = 8; 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((( cf==1  && (input == 2)) && (a16 == 32 && (((a37 == 11 && (a150 == 32 && a24 == 32)) && a170 == 6) && a24 == 32)))) {
    	cf = 0;
    	a56 = 9;
    	a39 = 3;
    	a79 = 10;
    	a111 = 11;
    	a0 = 12;
    	a25 = 34 ;
    	a82 = 7;
    	a200 = 34 ;
    	a24 = 34 ;
    	a60 = 34 ;
    	a188 = 5;
    	a16 = 34 ;
    	a191 = 34 ;
    	a41 = 3;
    	a182 = 10; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a37 == 11 && (a95 == 10 && ((input == 5) &&  cf==1 ))) && (((a86 == 32 && a16 == 32) && a82 == 6) && a168 == 8))) {
    	cf = 0;
    	a109 = 7;
    	a110 = 8; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((((( cf==1  && (input == 1)) && a95 == 10) && a24 == 32) && a39 == 2) && ((a15 == 11 && a79 == 9) && a111 == 10))) {
    	cf = 0;
    	a0 = 10;
    	a95 = 9;
    	a25 = 33 ;
    	a14 = 33 ;
    	a56 = 7;
    	a41 = 1;
    	a39 = 1;
    	a197 = 33 ;
    	a111 = 9;
    	a191 = 33 ;
    	a24 = 33 ;
    	a63 = 33 ;
    	a86 = 33 ;
    	a82 = 5;
    	a79 = 8;
    	a196 = 33 ;
    	a69 = 32 ;
    	a150 = 33 ;
    	a15 = 10;
    	a37 = 10;
    	a168 = 7;
    	a92 = 4;
    	a7 = 4;
    	a200 = 33 ;
    	a91 = 10; 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm33(int input) {
    if(((((a200 == 32 && (a191 == 32 && a86 == 32)) && a79 == 9) && a25 == 32) && (( cf==1  && a130 == 13) && a82 == 6))) {
    	calculate_outputm137(input);
    } 
}

 void calculate_output(int input) {
        cf = 1;

    if(((a7 == 4 && ((a63 == 33 && (a197 == 33 && ( cf==1  && a56 == 7))) && a86 == 33)) && (a0 == 10 && a150 == 33))) {
    	if(((((a200 == 33 && ( cf==1  && a69 == 32)) && a63 == 33) && a196 == 33) && (a95 == 9 && (a79 == 8 && a63 == 33)))) {
    		calculate_outputm2(input);
    	} 
    } 
    if(((a142 == 6 && (a25 == 32 && (a7 == 5 && a79 == 9))) && (a188 == 4 && (( cf==1  && a56 == 8) && a150 == 32)))) {
    	if(((a164 == 32 && (a86 == 32 && a111 == 10)) && (a111 == 10 && ((a95 == 10 && ( cf==1  && a160 == 2)) && a82 == 6)))) {
    		calculate_outputm6(input);
    	} 
    	if((((a142 == 6 && a142 == 6) && a7 == 5) && ((a111 == 10 && (a14 == 32 && (a160 == 6 &&  cf==1 ))) && a24 == 32))) {
    		calculate_outputm10(input);
    	} 
    	if(((a191 == 32 && (a86 == 32 && ((a197 == 32 && (a197 == 32 && (a160 == 7 &&  cf==1 ))) && a37 == 11))) && a191 == 32)) {
    		calculate_outputm11(input);
    	} 
    } 
    if(((((a24 == 34 && (a200 == 34 && (a56 == 9 &&  cf==1 ))) && a111 == 11) && a41 == 3) && (a25 == 34 && a16 == 34))) {
    	if(((a196 == 34 && a170 == 7) && ((a142 == 7 && ((( cf==1  && a60 == 35) && a7 == 6) && a63 == 34)) && a150 == 34))) {
    		calculate_outputm17(input);
    	} 
    	if((((a15 == 12 && (a164 == 34 && a0 == 12)) && a92 == 6) && (a197 == 34 && ((a60 == 36 &&  cf==1 ) && a63 == 34)))) {
    		calculate_outputm18(input);
    	} 
    } 
    if(((a168 == 8 && (a56 == 10 &&  cf==1 )) && (a168 == 8 && (a142 == 6 && (a14 == 32 && (a16 == 32 && a170 == 6)))))) {
    	if((((a196 == 32 && (a41 == 2 && a86 == 32)) && a82 == 6) && (a200 == 32 && ((a160 == 3 &&  cf==1 ) && a25 == 32)))) {
    		calculate_outputm20(input);
    	} 
    	if((( cf==1  && a160 == 4) && (((a79 == 9 && ((a0 == 11 && a25 == 32) && a188 == 4)) && a24 == 32) && a170 == 6))) {
    		calculate_outputm21(input);
    	} 
    	if(((a196 == 32 && ((a30 == 32 && ( cf==1  && a160 == 9)) && a168 == 8)) && (a39 == 2 && (a191 == 32 && a196 == 32)))) {
    		calculate_outputm24(input);
    	} 
    } 
    if((((a168 == 8 && (a14 == 32 && ( cf==1  && a56 == 12))) && a120 == 32) && ((a16 == 32 && a7 == 5) && a170 == 6))) {
    	if(((a131 == 32 && (a41 == 2 && (a109 == 4 &&  cf==1 ))) && (a82 == 6 && ((a86 == 32 && a25 == 32) && a191 == 32)))) {
    		calculate_outputm29(input);
    	} 
    	if(((((a191 == 32 && a0 == 11) && a168 == 8) && a92 == 5) && (a95 == 10 && ((a109 == 7 &&  cf==1 ) && a14 == 32)))) {
    		calculate_outputm32(input);
    	} 
    	if(((a200 == 32 && (a79 == 9 && a196 == 32)) && (((a142 == 6 && (a109 == 8 &&  cf==1 )) && a200 == 32) && a200 == 32))) {
    		calculate_outputm33(input);
    	} 
    } 
    errorCheck();

    if( cf==1 ) {
    	fprintf(stdout, "Invalid input: %d\n", input);
    	ERR = ERR_INVALID_INPUT;
    }
}
