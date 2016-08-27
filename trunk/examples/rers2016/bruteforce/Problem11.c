#include <stdio.h> 
#include <assert.h>
#include <math.h>
#include <stdlib.h>

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

	 int a58 = 5;
	 int a172 = 3;
	 int a187 = -193;
	 int a130 = 4;
	 int a147 = 10;
	 int a117 = 9;
	 int a100 = -50;
	 int a184 = 4;
	 int a167 = 9;
	 int a181 = 252;
	 int a159 = 143;
	 int a0 = 12;
	 int a148 = -59;
	 int cf = 1;
	 int a83 = 10;
	 int a156 = 34;
	 int a66 = 4;
	 int a28 = 167;
	 int a102 = 194;
	 int a166 = 12;
	 int a27 = 8;
	 int a90 = 12;
	 int a45 = 6;
	 int a81 = 65;
	 int a26 = 3;
	 int a16 = 118;
	 int a39 = 7;
	 int a120 = 145;
	 int a169 = 159;
	 int a7 = 254;
	 int a158 = 411;
	 int a121 = 9;
	 int a119 = 6;
	 int a72 = 11;
	 int a176 = 1;
	 int a196 = 14;
	 int a1 = 104;
	 int a78 = 183;
	 int a61 = 10;
	 int a157 = 13;
	 int a75 = 8;
	 int a9 = 152;
	 int a180 = 70;
	 int a195 = 4;
	 int a17 = 1;
	 int a43 = 1;
	 int a164 = 0;
	 int a101 = 1;
	 int a71 = 1;
	 int a68 = 1;
	 int a197 = 1;
	 int a60 = 1;
	 int a12 = 1;
	 int a138 = 3;
	 int a33 = 1;
	 int a50 = 1;
	 int a131 = -15;
	 int a137 = 1;
	 int a67 = 1;
	 int a177 = 1;
	 int a89 = 1;
	 int a122 = -15;
	 int a76 = 1;
	 int a112 = 1;
	 int a15 = 1;
	 int a191 = 3;
	 int a64 = 3;
	 int a151 = 1;
	 int a99 = -15;
	 int a152 = 3;
	 int a106 = 1;
	 int a97 = 1;
	 int a88 = 2;
	 int a183 = 1;
	 int a135 = -15;
	 int a25 = 1;
	 int a182 = 0;
	 int a5 = 1;
	 int a108 = 1;
	 int a186 = -15;
	 int a34 = -15;
	 int a42 = 1;
         
         void reset_eca() {
         a58 = 5;
	 a172 = 3;
	 a187 = -193;
	 a130 = 4;
	 a147 = 10;
	 a117 = 9;
	 a100 = -50;
	 a184 = 4;
	 a167 = 9;
	 a181 = 252;
	 a159 = 143;
	 a0 = 12;
	 a148 = -59;
	 cf = 1;
	 a83 = 10;
	 a156 = 34;
	 a66 = 4;
	 a28 = 167;
	 a102 = 194;
	 a166 = 12;
	 a27 = 8;
	 a90 = 12;
	 a45 = 6;
	 a81 = 65;
	 a26 = 3;
	 a16 = 118;
	 a39 = 7;
	 a120 = 145;
	 a169 = 159;
	 a7 = 254;
	 a158 = 411;
	 a121 = 9;
	 a119 = 6;
	 a72 = 11;
	 a176 = 1;
	 a196 = 14;
	 a1 = 104;
	 a78 = 183;
	 a61 = 10;
	 a157 = 13;
	 a75 = 8;
	 a9 = 152;
	 a180 = 70;
	 a195 = 4;
	 a17 = 1;
	 a43 = 1;
	 a164 = 0;
	 a101 = 1;
	 a71 = 1;
	 a68 = 1;
	 a197 = 1;
	 a60 = 1;
	 a12 = 1;
	 a138 = 3;
	 a33 = 1;
	 a50 = 1;
	 a131 = -15;
	 a137 = 1;
	 a67 = 1;
	 a177 = 1;
	 a89 = 1;
	 a122 = -15;
	 a76 = 1;
	 a112 = 1;
	 a15 = 1;
	 a191 = 3;
	 a64 = 3;
	 a151 = 1;
	 a99 = -15;
	 a152 = 3;
	 a106 = 1;
	 a97 = 1;
	 a88 = 2;
	 a183 = 1;
	 a135 = -15;
	 a25 = 1;
	 a182 = 0;
	 a5 = 1;
	 a108 = 1;
	 a186 = -15;
	 a34 = -15;
	 a42 = 1;
         }
         


	void errorCheck() {
	    if(((a121 == 2 && a66 == 4) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(0);
	    }
	    if(((a90 == 10 && ((-73 < a148) && (32 >= a148))) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(1);
	    }
	    if(((a121 == 6 && a66 == 4) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(2);
	    }
	    if(((a169 <=  175 && a45 == 5) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(3);
	    }
	    if(((a121 == 5 && a66 == 4) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(4);
	    }
	    if(((a119 == 6 && a66 == 5) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(5);
	    }
	    if(((a90 == 14 && ((-73 < a148) && (32 >= a148))) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(6);
	    }
	    if(((a119 == 10 && a66 == 5) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(7);
	    }
	    if(((286 < a1 && a66 == 9) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(8);
	    }
	    if(((a195 == 4 && a66 == 8) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(9);
	    }
	    if(((a0 == 14 && ((137 < a7) && (246 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(10);
	    }
	    if(((a0 == 11 && ((137 < a7) && (246 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(11);
	    }
	    if(((((254 < a169) && (433 >= a169)) && a45 == 5) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(12);
	    }
	    if(((((247 < a181) && (412 >= a181)) && a45 == 4) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(13);
	    }
	    if(((a72 == 10 && a45 == 2) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(14);
	    }
	    if(((a157 == 9 && a45 == 6) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(15);
	    }
	    if(((a196 == 15 && a66 == 6) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(16);
	    }
	    if(((((108 < a78) && (219 >= a78)) && a148 <=  -73) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(17);
	    }
	    if(((((162 < a181) && (247 >= a181)) && a45 == 4) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(18);
	    }
	    if(((((162 < a181) && (247 >= a181)) && a45 == 3) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(19);
	    }
	    if(((a158 <=  114 && a45 == 7) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(20);
	    }
	    if(((a157 == 12 && a45 == 6) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(21);
	    }
	    if(((a181 <=  162 && a45 == 3) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(22);
	    }
	    if(((((263 < a158) && (424 >= a158)) && a45 == 7) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(23);
	    }
	    if(((a166 == 11 && a66 == 2) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(24);
	    }
	    if(((a166 == 12 && a66 == 2) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(25);
	    }
	    if(((344 < a28 && 246 < a7) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(26);
	    }
	    if(((a196 == 13 && a66 == 6) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(27);
	    }
	    if(((a195 == 6 && a66 == 8) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(28);
	    }
	    if(((a195 == 10 && a66 == 8) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(29);
	    }
	    if(((a119 == 8 && a66 == 5) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(30);
	    }
	    if(((a195 == 6 && a45 == 8) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(31);
	    }
	    if(((a166 == 9 && a66 == 2) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(32);
	    }
	    if(((a172 == 10 && a66 == 3) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(33);
	    }
	    if(((a0 == 10 && ((137 < a7) && (246 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(34);
	    }
	    if(((((175 < a169) && (254 >= a169)) && a45 == 5) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(35);
	    }
	    if(((a196 == 14 && a66 == 6) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(36);
	    }
	    if(((a39 == 8 && a45 == 1) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(37);
	    }
	    if(((a1 <=  -21 && a66 == 9) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(38);
	    }
	    if(((a172 == 6 && a66 == 3) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(39);
	    }
	    if(((a196 == 12 && a66 == 6) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(40);
	    }
	    if(((a0 == 12 && ((137 < a7) && (246 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(41);
	    }
	    if(((a172 == 7 && a66 == 3) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(42);
	    }
	    if(((a176 == 1 && ((54 < a7) && (137 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(43);
	    }
	    if(((a167 == 14 && 162 < a148) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(44);
	    }
	    if(((a119 == 5 && a66 == 5) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(45);
	    }
	    if(((a90 == 13 && ((-73 < a148) && (32 >= a148))) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(46);
	    }
	    if(((a167 == 12 && 162 < a148) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(47);
	    }
	    if(((((133 < a28) && (253 >= a28)) && 246 < a7) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(48);
	    }
	    if(((a39 == 7 && a45 == 1) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(49);
	    }
	    if(((a121 == 8 && a66 == 4) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(50);
	    }
	    if(((a167 == 8 && 162 < a148) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(51);
	    }
	    if(((a195 == 9 && a66 == 8) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(52);
	    }
	    if(((219 < a78 && a66 == 7) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(53);
	    }
	    if(((a176 == 2 && ((54 < a7) && (137 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(54);
	    }
	    if(((a157 == 6 && a45 == 6) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(55);
	    }
	    if(((a90 == 12 && ((-73 < a148) && (32 >= a148))) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(56);
	    }
	    if(((a72 == 12 && a45 == 2) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(57);
	    }
	    if(((a157 == 8 && a45 == 6) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(58);
	    }
	    if(((((147 < a1) && (286 >= a1)) && a66 == 9) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(59);
	    }
	    if(((a172 == 9 && a66 == 3) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(60);
	    }
	    if(((a166 == 14 && a66 == 2) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(61);
	    }
	    if(((a157 == 7 && a45 == 6) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(62);
	    }
	    if(((a119 == 9 && a66 == 5) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(63);
	    }
	    if(((a195 == 11 && a66 == 8) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(64);
	    }
	    if(((((-40 < a78) && (108 >= a78)) && a148 <=  -73) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(65);
	    }
	    if(((a176 == 3 && ((54 < a7) && (137 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(66);
	    }
	    if(((((-40 < a78) && (108 >= a78)) && a66 == 7) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(67);
	    }
	    if(((a195 == 7 && a66 == 8) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(68);
	    }
	    if(((a121 == 7 && a66 == 4) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(69);
	    }
	    if(((a39 == 13 && a45 == 1) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(70);
	    }
	    if(((a180 <=  -46 && ((32 < a148) && (162 >= a148))) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(71);
	    }
	    if(((a196 == 17 && a66 == 6) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(72);
	    }
	    if(((a176 == 5 && ((54 < a7) && (137 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(73);
	    }
	    if(((a181 <=  162 && a7 <=  54) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(74);
	    }
	    if(((a195 == 5 && a66 == 8) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(75);
	    }
	    if(((a72 == 11 && a45 == 2) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(76);
	    }
	    if(((a121 == 4 && a66 == 4) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(77);
	    }
	    if(((a39 == 10 && a45 == 1) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(78);
	    }
	    if(((a172 == 3 && a66 == 3) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(79);
	    }
	    if(((((253 < a28) && (344 >= a28)) && 246 < a7) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(80);
	    }
	    if(((a90 == 16 && ((-73 < a148) && (32 >= a148))) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(81);
	    }
	    if(((a0 == 7 && ((137 < a7) && (246 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(82);
	    }
	    if(((a0 == 8 && ((137 < a7) && (246 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(83);
	    }
	    if(((a90 == 17 && ((-73 < a148) && (32 >= a148))) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(84);
	    }
	    if(((a167 == 7 && 162 < a148) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(85);
	    }
	    if(((a167 == 13 && 162 < a148) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(86);
	    }
	    if(((a196 == 16 && a66 == 6) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(87);
	    }
	    if(((a39 == 12 && a45 == 1) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(88);
	    }
	    if(((a176 == 8 && ((54 < a7) && (137 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(89);
	    }
	    if(((a167 == 10 && 162 < a148) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(90);
	    }
	    if(((412 < a181 && a45 == 3) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(91);
	    }
	    if(((a195 == 5 && a45 == 8) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(92);
	    }
	    if(((a28 <=  133 && 246 < a7) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(93);
	    }
	    if(((a166 == 13 && a66 == 2) && a100 <=  -30)){
	    cf = 0;
	    __VERIFIER_error(94);
	    }
	    if(((412 < a181 && a45 == 4) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(95);
	    }
	    if(((219 < a78 && a148 <=  -73) && 143 < a100)){
	    cf = 0;
	    __VERIFIER_error(96);
	    }
	    if(((a176 == 7 && ((54 < a7) && (137 >= a7))) && ((44 < a100) && (143 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(97);
	    }
	    if(((a39 == 9 && a45 == 1) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(98);
	    }
	    if(((a157 == 10 && a45 == 6) && ((-30 < a100) && (44 >= a100)))){
	    cf = 0;
	    __VERIFIER_error(99);
	    }
	}
 void calculate_outputm30(int input) {
    if((((a130 == 4 && a81 <=  84) && (((a156 <=  44 && (a27 == 8 && ( cf==1  && (input == 5)))) && a58 <=  11) && a26 == 3)) && a183 <= -29)) {
    	a33 += (a33 + 20) > a33 ? 4 : 0;
    	cf = 0;
    	a102 = ((((((((a102 * a16) % 14999) + 2037) % 58) + 254) * 5) % 58) - -228);
    	a45 = ((a26 + a130) - -1);
    	a81 = ((((((a81 * a159) % 14999) % 93) + 179) * 1) + -1);
    	a100 = ((((((a100 * a9) % 14999) % 36) + 6) - -1) + 1);
    	a195 = (a66 + 4);
    	a184 = (a147 + -5);
    	a9 = (((((((a187 * a102) % 14999) % 31) - -192) * 1) - 18801) + 18801);
    	a159 = (((((((((a81 * a81) % 14999) % 32) - -171) * 9) / 10) * 5) % 32) + 174);
    	a75 = a117;
    	a61 = (a166 + -4);
    	a120 = (((((((a120 * a81) % 14999) % 58) - -205) - 30139) * 1) - -30138);
    	a147 = (a27 - -3); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((((((input == 4) &&  cf==1 ) && a102 <=  196) && a147 == 10) && (a58 <=  11 && ((a187 <=  -176 && a27 == 8) && a156 <=  44))) && a97 <= -3)) {
    	a68 += (a68 + 20) > a68 ? 3 : 0;
    	cf = 0;
    	a119 = (a147 + -1);
    	a66 = (a184 + 1); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((((a9 <=  159 && ((input == 1) &&  cf==1 )) && a159 <=  150) && (a83 == 10 && ((a26 == 3 && a61 == 10) && a58 <=  11))) && a88 >= 12)) {
    	a137 += (a137 + 20) > a137 ? 2 : 0;
    	cf = 0;
    	a147 = (a61 - -1);
    	a187 = ((((((a187 * a156) % 14999) / 5) - -20102) % 107) + -164);
    	a130 = (a147 - 6);
    	a117 = (a130 - -5);
    	a100 = ((((((a100 * a120) % 14999) / 5) / 5) % 36) + 8);
    	a184 = a130;
    	a102 = ((((((((a58 * a156) % 14999) * 2) % 58) + 256) * 5) % 58) - -256);
    	a45 = (a166 + -10);
    	a169 = ((((((a159 * a159) % 14999) * 2) - 3) % 89) - -343);
    	a120 = ((((((a120 * a9) % 14999) % 58) + 205) - -1) - 2);
    	a9 = ((((((a159 * a159) % 14999) % 31) + 190) - 0) - -2);
    	a156 = ((((((a156 * a102) % 14999) + 13390) / 5) % 61) + 106);
    	a159 = ((((((((a159 * a16) % 14999) % 32) + 183) * 1) / 5) * 51) / 10); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a81 <=  84 && a117 == 9) && ((((a26 == 3 && ((input == 3) &&  cf==1 )) && a102 <=  196) && a27 == 8) && a81 <=  84))) {
    	a68 += (a68 + 20) > a68 ? 2 : 0;
    	cf = 0;
    	a66 = ((a184 * a130) - 13);
    	a172 = (a26 + 2); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((a83 == 10 && ((input == 2) &&  cf==1 )) && a117 == 9) && (((a159 <=  150 && a117 == 9) && a16 <=  125) && a102 <=  196))) {
    	cf = 0;
    	 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm1(int input) {
    if(((((((a166 == 15 &&  cf==1 ) && a16 <=  125) && a83 == 10) && a120 <=  146) && a81 <=  84) && (a117 == 9 && a184 == 4))) {
    	calculate_outputm30(input);
    } 
}
 void calculate_outputm32(int input) {
    if(((a26 == 3 && (a184 == 4 && ( cf==1  && (input == 3)))) && (a58 <=  11 && (a26 == 3 && (a61 == 10 && a187 <=  -176))))) {
    	cf = 0;
    	a9 = ((((((a81 * a156) % 14999) / 5) * 5) % 34) - -257);
    	a90 = (a61 + 5);
    	a187 = ((((((a9 * a81) % 14999) + -1312) % 99) + 138) - -2);
    	a148 = ((((((((a102 * a159) % 14999) % 52) + -19) + -2) * 5) % 52) - 19);
    	a16 = (((((((a16 * a102) % 14999) % 54) + 344) - -1) / 5) - -306);
    	a58 = ((((((a58 * a81) % 14999) % 69) - -212) + 10671) + -10670);
    	a100 = (((((((a100 * a148) % 14999) - -11750) + 935) - 5394) % 14928) - -15071);
    	a61 = (a90 + -3);
    	a117 = (a26 - -8);
    	a75 = (a66 - -7);
    	a147 = (a26 + 9);
    	a26 = (a75 + -5);
    	a156 = (((((((a156 * a9) % 14999) % 104) + 274) + 1) / 5) - -237);
    	a102 = (((((((a81 * a120) % 14999) - 2316) + -9122) + 8984) % 83) - -398);
    	a159 = ((((((a159 * a58) % 14999) + 9187) % 38) + 255) + -1);
    	a130 = (a66 - -3);
    	a184 = (a172 - -1);
    	a83 = (a66 - -9);
    	a120 = (((((((a9 * a9) % 14999) % 101) - -328) * 9) / 10) + 69);
    	a27 = (a83 - 2);
    	a81 = (((((((a81 * a187) % 14999) % 41) - -313) * 5) % 41) + 301); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((((a75 == 8 && a26 == 3) && a147 == 10) && a81 <=  84) && ((a102 <=  196 && ( cf==1  && (input == 5))) && a130 == 4))) {
    	a89 += (a89 + 20) > a89 ? 1 : 0;
    	cf = 0;
    	a26 = a130;
    	a45 = ((a172 / a61) - -1);
    	a100 = ((((((((a100 * a9) % 14999) % 36) + 7) - 1) * 5) % 36) + 8);
    	a39 = ((a184 + a45) - -6);
    	a120 = (((((((a9 * a159) % 14999) + 4718) % 58) + 205) - -18500) - 18500);
    	a27 = (a172 - -4);
    	a81 = ((((((a81 * a159) % 14999) % 93) + 177) - 0) * 1);
    	a61 = (a26 + 7);
    	a102 = (((((((a187 * a16) % 14999) + -4951) * 1) * 1) % 58) + 256);
    	a147 = a39;
    	a58 = ((((((((a58 * a102) % 14999) % 65) - -77) * 1) * 5) % 65) - -12);
    	a130 = (a75 + -3);
    	a184 = (a27 - 4);
    	a117 = (a26 - -6);
    	a83 = (a26 + 7);
    	a187 = ((((((a156 * a156) % 14999) % 107) - 68) / 5) + -27);
    	a156 = ((((((a120 * a9) % 14999) % 61) + 105) / 5) - -126);
    	a16 = (((((((a16 * a159) % 14999) / 5) % 82) - -207) - 7111) - -7111);
    	a75 = (a66 + 6);
    	a9 = ((((((a9 * a159) % 14999) / 5) / 5) % 31) - -192); 
    	 printf("%d\n", 22); fflush(stdout); 
    } 
    if(((((a159 <=  150 && (a27 == 8 && (((input == 1) &&  cf==1 ) && a156 <=  44))) && a102 <=  196) && (a75 == 8 && a58 <=  11)) && a17 == 3262)) {
    	a164 -= (a164 - 20) < a164 ? 1 : 0;
    	cf = 0;
    	a181 = (((((((a159 * a120) % 14999) % 82) - -330) * 1) + 29153) + -29152);
    	a45 = (a75 - 4);
    	a100 = ((((((((a100 * a159) % 14999) * 2) % 36) - -7) * 5) % 36) - -7); 
    	 printf("%d\n", 19); fflush(stdout); 
    } 
    if((((a159 <=  150 && (a102 <=  196 && ( cf==1  && (input == 4)))) && ((a147 == 10 && (a156 <=  44 && a159 <=  150)) && a156 <=  44)) && a43 >= 1)) {
    	a43 -= (a43 - 20) < a43 ? 2 : 0;
    	cf = 0;
    	a120 = ((((((a81 * a81) % 14999) % 58) - -204) - 0) + 2);
    	a156 = (((((((a120 * a120) % 14999) % 61) - -100) + 4) + 29795) - 29840);
    	a184 = (a130 + 1);
    	a45 = (a147 - 8);
    	a72 = ((a147 - a75) - -9);
    	a102 = ((((((a102 * a159) % 14999) % 58) - -256) * 1) + 1);
    	a58 = ((((((a58 * a187) % 14999) / 5) % 65) - -77) - -1);
    	a16 = ((((((a16 * a156) % 14999) % 82) + 208) * 1) * 1);
    	a117 = (a184 + 5);
    	a100 = ((((((a100 * a9) % 14999) + -353) + 9214) % 36) + 7);
    	a27 = ((a147 - a26) - -2);
    	a75 = ((a61 - a172) - -4);
    	a9 = (((((((a81 * a156) % 14999) % 31) - -191) + 29083) + 364) + -29447);
    	a147 = (a66 + 8); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((a75 == 8 && a117 == 9) && a26 == 3) && ((a159 <=  150 && (( cf==1  && (input == 2)) && a61 == 10)) && a83 == 10))) {
    	a138 += (a138 + 20) > a138 ? 2 : 0;
    	a131 += (a131 + 20) > a131 ? 2 : 0;
    	a137 -= (a137 - 20) < a137 ? 4 : 0;
    	a67 -= (a67 - 20) < a67 ? 2 : 0;
    	a89 -= (a89 - 20) < a89 ? 4 : 0;
    	a152 += (a152 + 20) > a152 ? 1 : 0;
    	a106 -= (a106 - 20) < a106 ? 2 : 0;
    	a88 += (a88 + 20) > a88 ? 2 : 0;
    	a182 += (a182 + 20) > a182 ? 2 : 0;
    	cf = 0;
    	a66 = ((a172 - a130) + 5);
    	a196 = (a172 - -6); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm35(int input) {
    if((((input == 2) &&  cf==1 ) && ((((a83 == 10 && (a117 == 9 && a120 <=  146)) && a120 <=  146) && a9 <=  159) && a156 <=  44))) {
    	cf = 0;
    	a66 = (a83 + -4);
    	a196 = (a61 + 1); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a16 <=  125 && ((( cf==1  && (input == 3)) && a83 == 10) && a58 <=  11)) && (a61 == 10 && (a83 == 10 && a130 == 4)))) {
    	a76 -= (a76 - 20) < a76 ? 4 : 0;
    	a151 -= (a151 - 20) < a151 ? 3 : 0;
    	cf = 0;
    	a39 = (a26 + 8);
    	a45 = (a27 + -7);
    	a100 = ((((((a100 * a187) % 14999) % 36) + -26) + -3) + 2);
    	a58 = ((((((a58 * a159) % 14999) - 11039) % 65) - -77) - -1);
    	a184 = (a117 + -4);
    	a27 = (a172 + 1);
    	a120 = (((((((a120 * a81) % 14999) * 2) % 58) + 205) / 5) + 165);
    	a75 = ((a39 + a39) + -13);
    	a102 = ((((((a159 * a81) % 14999) * 2) % 58) + 256) * 1);
    	a147 = ((a27 - a130) + 6);
    	a156 = ((((((a156 * a16) % 14999) % 61) - -105) / 5) * 5);
    	a187 = ((((((a100 * a9) % 14999) + 14124) % 107) + -67) + -1);
    	a26 = ((a45 * a45) - -3);
    	a16 = (((((a100 * a100) % 82) + 207) * 1) - -1);
    	a117 = ((a75 + a83) - 9);
    	a61 = ((a66 * a66) - -2);
    	a83 = (a45 - -10);
    	a130 = ((a61 * a45) + -6);
    	a9 = (((((((a9 * a58) % 14999) % 31) + 191) * 1) + -24461) - -24462);
    	a81 = ((((((a81 * a102) % 14999) % 93) - -179) * 5) / 5); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm2(int input) {
    if((((a159 <=  150 && a58 <=  11) && a58 <=  11) && (a117 == 9 && (a147 == 10 && ((a172 == 5 &&  cf==1 ) && a16 <=  125))))) {
    	calculate_outputm32(input);
    } 
    if(((a184 == 4 && (a81 <=  84 && a117 == 9)) && (a147 == 10 && ((a156 <=  44 && (a172 == 8 &&  cf==1 )) && a120 <=  146)))) {
    	calculate_outputm35(input);
    } 
}
 void calculate_outputm39(int input) {
    if((((a27 == 8 && a159 <=  150) && (a156 <=  44 && ((a102 <=  196 && (a61 == 10 && ((input == 1) &&  cf==1 ))) && a9 <=  159))) && a67 <= -3)) {
    	a68 += (a68 + 20) > a68 ? 2 : 0;
    	cf = 0;
    	a1 = (((((((a9 * a159) % 14999) - -14834) / 5) - -6116) * -1) / 10);
    	a66 = ((a75 * a26) + -15); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a156 <=  44 && (a75 == 8 && (a187 <=  -176 && a26 == 3))) && (a159 <=  150 && (a130 == 4 && ( cf==1  && (input == 5)))))) {
    	a60 += (a60 + 20) > a60 ? 1 : 0;
    	cf = 0;
    	a26 = ((a147 + a147) - 16);
    	a184 = (a147 + -5);
    	a16 = ((((36 * 10) / 2) - -65) + 25);
    	a100 = ((((((a100 * a9) % 14999) % 36) - -7) / 5) * 5);
    	a187 = ((((((a187 * a102) % 14999) % 107) - 68) - -1) - 2);
    	a81 = (((((((a81 * a16) % 14999) + -5849) % 93) - -178) / 5) - -192);
    	a120 = (((((((a120 * a156) % 14999) * 2) + 1) - -1) % 58) - -205);
    	a83 = ((a147 * a147) - 89);
    	a75 = ((a27 * a184) - 31);
    	a45 = a27;
    	a102 = (((((((a58 * a58) % 14999) - 14015) * 1) + -710) % 58) + 256);
    	a58 = ((((((a58 * a159) % 14999) % 65) + 76) - -1) + 1);
    	a61 = ((a66 + a66) - -3);
    	a27 = ((a117 + a121) + -3);
    	a9 = ((((((a9 * a187) % 14999) / 5) % 31) - -191) - 1);
    	a159 = (((68 * 5) / 5) + 103);
    	a130 = (a147 - 5);
    	a195 = a45;
    	a117 = (a184 - -5);
    	a147 = ((a130 - a130) - -11); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a102 <=  196 && ((a102 <=  196 && ( cf==1  && (input == 2))) && a61 == 10)) && ((a58 <=  11 && a75 == 8) && a75 == 8))) {
    	a135 += (a135 + 20) > a135 ? 2 : 0;
    	a183 += (a183 + 20) > a183 ? 2 : 0;
    	cf = 0;
    	a16 = (((87 - 6940) + 6995) + 146);
    	a83 = (a121 + 8);
    	a184 = (a130 - -1);
    	a102 = ((((((a16 * a16) % 14999) % 58) + 206) + 20383) - 20338);
    	a45 = (a147 + -2);
    	a81 = (((((((a81 * a102) % 14999) - -13181) * 1) * 1) % 93) + 178);
    	a156 = ((((((a156 * a187) % 14999) % 61) - -105) * 1) + 0);
    	a100 = ((((((a100 * a58) % 14999) % 36) - -6) - -2) - 1);
    	a120 = (((((((a120 * a9) % 14999) % 58) - -204) * 5) % 58) + 184);
    	a195 = (a66 + 7);
    	a58 = ((((((a9 * a9) % 14999) % 69) - -211) - -27664) + -27662);
    	a75 = (a117 - -1);
    	a61 = a83;
    	a187 = (((((((a187 * a159) % 14999) - -12668) - 8190) / 5) % 107) - 68);
    	a27 = (a26 + 7);
    	a117 = ((a130 * a184) - 10);
    	a9 = (((((((a9 * a81) % 14999) % 31) - -190) * 1) + -3902) + 3904);
    	a147 = ((a26 / a83) - -11);
    	a159 = ((((((a16 * a16) % 14999) / 5) % 32) - -162) * 1);
    	a26 = (a83 + -7);
    	a130 = (a83 - 5); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((a159 <=  150 && ((a58 <=  11 && (( cf==1  && (input == 3)) && a83 == 10)) && a26 == 3)) && (a26 == 3 && a9 <=  159))) {
    	a43 -= (a43 - 20) < a43 ? 1 : 0;
    	cf = 0;
    	a7 = (((((((a159 * a9) % 14999) % 54) - -191) / 5) / 5) + 142);
    	a16 = (((((((a7 * a7) % 14999) + -384) % 54) - -345) - -11774) + -11773);
    	a130 = ((a66 + a121) - 1);
    	a0 = (a75 - -5);
    	a61 = (a27 + 4);
    	a81 = (((((((a16 * a7) % 14999) + 1037) % 41) + 304) * 9) / 10);
    	a100 = ((((((a100 * a102) % 14999) % 49) + 94) + -23989) - -23989);
    	a102 = ((((((a7 * a58) % 14999) % 83) - -398) - 1) + 0);
    	a156 = ((((((a156 * a81) % 14999) % 104) - -272) - 0) + 3);
    	a187 = (((((((a187 * a102) % 14999) - 7176) + -789) + 37474) % 99) - -74);
    	a58 = (((((((a58 * a16) % 14999) % 69) + 211) - 20901) - 2847) - -23748);
    	a184 = a130;
    	a9 = ((((((a16 * a7) % 14999) % 34) + 237) - 12) - -8);
    	a75 = (a27 + 2);
    	a120 = (((((((a120 * a156) % 14999) % 101) + 365) - -1) - -26923) + -26924);
    	a117 = (a130 + 5);
    	a159 = (((((((a7 * a7) % 14999) / 5) - 29767) * 1) % 38) + 261);
    	a147 = ((a130 * a26) - 6);
    	a27 = a83;
    	a83 = (a26 + 9);
    	a26 = (a66 + 1); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((a159 <=  150 && (( cf==1  && (input == 4)) && a147 == 10)) && (a83 == 10 && (a187 <=  -176 && (a61 == 10 && a187 <=  -176)))) && a177 == 86)) {
    	a182 -= (a182 - 20) < a182 ? 3 : 0;
    	cf = 0;
    	a166 = (a27 - -3);
    	a66 = (a184 - 2); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm45(int input) {
    if(((a61 == 10 && (a27 == 8 && ((input == 5) &&  cf==1 ))) && (((a16 <=  125 && a83 == 10) && a16 <=  125) && a120 <=  146))) {
    	cf = 0;
    	a9 = ((((((a9 * a156) % 14999) % 31) - -192) / 5) + 175);
    	a81 = (((((((a9 * a9) % 14999) + 1682) % 93) + 174) * 9) / 10);
    	a45 = ((a75 - a26) + 1);
    	a120 = (((((((a120 * a81) % 14999) - -10955) - 2401) - -679) % 58) - -205);
    	a100 = ((((((a100 * a159) % 14999) - -9296) % 36) - -7) / 5);
    	a147 = (a27 - -3);
    	a16 = (((((((a9 * a81) % 14999) + 3216) % 82) - -129) + -19435) + 19445);
    	a184 = (a75 - 3);
    	a26 = (a117 - 5);
    	a157 = (a66 + 7);
    	a61 = (a27 + 3);
    	a102 = ((((((a102 * a187) % 14999) % 58) + 255) + 2) * 1);
    	a83 = (a45 + 5);
    	a187 = (((((((a187 * a9) % 14999) % 107) - 68) - -6152) + -7963) + 1810);
    	a58 = (((((((a16 * a16) % 14999) - 9303) % 65) + 77) + 21073) - 21072);
    	a130 = ((a121 * a147) + -94);
    	a27 = ((a61 / a147) - -8);
    	a75 = 9; 
    	 printf("%d\n", 20); fflush(stdout); 
    } 
}
 void calculate_outputm3(int input) {
    if((((a120 <=  146 && (a81 <=  84 && a75 == 8)) && a75 == 8) && ((a156 <=  44 && ( cf==1  && a121 == 3)) && a187 <=  -176))) {
    	calculate_outputm39(input);
    } 
    if((((a16 <=  125 && (a102 <=  196 && (( cf==1  && a121 == 9) && a102 <=  196))) && a61 == 10) && (a75 == 8 && a9 <=  159))) {
    	calculate_outputm45(input);
    } 
}
 void calculate_outputm51(int input) {
    if((((a26 == 3 && a26 == 3) && ((a102 <=  196 && ((a83 == 10 && ((input == 4) &&  cf==1 )) && a156 <=  44)) && a58 <=  11)) && a60 <= -21)) {
    	a60 += (a60 + 20) > a60 ? 3 : 0;
    	cf = 0;
    	a117 = (a196 - 1);
    	a81 = ((((((a159 * a58) % 14999) % 93) + 179) + 1) + -2);
    	a75 = (a117 - 1);
    	a9 = ((((((((a9 * a81) % 14999) % 31) + 191) + -1) * 5) % 31) - -185);
    	a39 = ((a66 - a83) + 11);
    	a147 = (a130 - -7);
    	a45 = (a196 + -10);
    	a100 = ((((((a100 * a102) % 14999) % 36) + 8) + 1) / 5);
    	a184 = (a26 + 2);
    	a120 = (((((((a120 * a58) % 14999) + -9097) + 19646) / 5) % 58) - -205);
    	a61 = (a130 - -7);
    	a102 = ((((((a102 * a187) % 14999) % 58) + 256) + 19084) + -19083);
    	a187 = ((((((((a187 * a58) % 14999) % 107) + -68) + 1) * 5) % 107) - 68);
    	a58 = ((((((a16 * a16) % 14999) % 65) - -77) * 5) / 5);
    	a26 = a130; 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((((a147 == 10 && ( cf==1  && (input == 1))) && a102 <=  196) && a117 == 9) && ((a81 <=  84 && a58 <=  11) && a9 <=  159)) && a197 >= 2)) {
    	a43 -= (a43 - 20) < a43 ? 1 : 0;
    	cf = 0;
    	a39 = ((a130 / a61) + 9);
    	a45 = (a83 + -9);
    	a117 = ((a39 + a196) - 10);
    	a100 = ((((((a100 * a159) % 14999) - 5976) % 36) - -6) - 0);
    	a9 = ((((((a9 * a156) % 14999) % 31) - -192) - 2) - -3);
    	a184 = (a45 - -4);
    	a27 = ((a75 - a66) - -7);
    	a26 = ((a39 - a45) - 4);
    	a120 = ((((((a58 * a58) % 14999) / 5) % 58) + 204) + 1);
    	a102 = ((((((((a102 * a120) % 14999) % 58) + 254) * 5) + -11906) % 58) + 262);
    	a81 = (((((((a81 * a187) % 14999) - -14995) - -4) / 5) % 93) - -135);
    	a147 = (a26 - -7);
    	a83 = (a39 + 2); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((a26 == 3 && (a27 == 8 && (((input == 5) &&  cf==1 ) && a81 <=  84))) && a130 == 4) && (a58 <=  11 && a187 <=  -176))) {
    	a152 -= (a152 - 20) < a152 ? 4 : 0;
    	cf = 0;
    	a66 = ((a147 + a184) - 7);
    	a78 = ((((((a100 * a9) % 14999) + -11362) % 14980) + -15019) - 2); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((a16 <=  125 && (a16 <=  125 && (a81 <=  84 && ( cf==1  && (input == 2))))) && (a120 <=  146 && (a61 == 10 && a187 <=  -176)))) {
    	a71 += (a71 + 20) > a71 ? 4 : 0;
    	a68 -= (a68 - 20) < a68 ? 4 : 0;
    	a197 += (a197 + 20) > a197 ? 1 : 0;
    	a60 -= (a60 - 20) < a60 ? 4 : 0;
    	a33 -= (a33 - 20) < a33 ? 2 : 0;
    	a108 += (a108 + 20) > a108 ? 4 : 0;
    	cf = 0;
    	a121 = ((a26 / a196) - -3);
    	a66 = (a147 + -6); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((a9 <=  159 && ((a83 == 10 && ((a9 <=  159 && a27 == 8) && a120 <=  146)) && a102 <=  196)) && ( cf==1  && (input == 3))) && a12 == 5576)) {
    	a106 += (a106 + 20) > a106 ? 1 : 0;
    	cf = 0;
    	a100 = ((((((a100 * a81) % 14999) + -9905) + -1867) % 14928) + 15071);
    	a167 = (a61 + 3);
    	a148 = (((((a102 * a81) % 14999) / 5) + 26292) + -7498); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm5(int input) {
    if((((a61 == 10 && (a75 == 8 && a102 <=  196)) && a81 <=  84) && (a9 <=  159 && (a75 == 8 && ( cf==1  && a196 == 11))))) {
    	calculate_outputm51(input);
    } 
}
 void calculate_outputm58(int input) {
    if((((a187 <=  -176 && (a26 == 3 && ( cf==1  && (input == 1)))) && (a58 <=  11 && ((a159 <=  150 && a61 == 10) && a27 == 8))) && a89 <= -1)) {
    	a88 += (a88 + 20) > a88 ? 2 : 0;
    	cf = 0;
    	a159 = ((((((a159 * a187) % 14999) % 38) + 256) / 5) - -231);
    	a184 = (a66 + -1);
    	a120 = (((((((a120 * a159) % 14999) / 5) % 101) + 365) + 4471) + -4470);
    	a26 = (a130 + 1);
    	a28 = (((((a9 * a100) % 14999) - 14970) / 5) - 9874);
    	a187 = ((((((a187 * a58) % 14999) * 2) % 99) + 139) - -1);
    	a83 = (a26 + 7);
    	a100 = ((((((((a100 * a28) % 14999) / 5) % 49) + 94) * 5) % 49) - -50);
    	a7 = ((((((a28 * a28) % 14999) % 14876) - -15122) - 0) * 1);
    	a61 = (a75 + 4);
    	a75 = (a130 - -6);
    	a117 = ((a130 + a184) - -1);
    	a130 = (a27 - 2);
    	a102 = ((((((a102 * a120) % 14999) % 83) + 399) - -1) + -2); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if((((a81 <=  84 && a102 <=  196) && a187 <=  -176) && (a16 <=  125 && ((((input == 3) &&  cf==1 ) && a102 <=  196) && a187 <=  -176)))) {
    	a17 += (a17 + 20) > a17 ? 2 : 0;
    	a183 -= (a183 - 20) < a183 ? 4 : 0;
    	cf = 0;
    	a26 = a184;
    	a75 = (a26 + 5);
    	a147 = (a75 + 2);
    	a27 = (a147 - 2);
    	a159 = ((((((((a159 * a58) % 14999) * 2) % 32) - -184) * 5) % 32) - -175);
    	a100 = (((((((a100 * a102) % 14999) * 2) + -2) + 0) % 36) - -6);
    	a58 = (((((((a58 * a16) % 14999) % 65) - -77) + 19699) / 5) + -3886);
    	a187 = ((((((a78 * a156) % 14999) / 5) * 5) % 107) - 67);
    	a45 = ((a130 / a130) + 3);
    	a83 = (a66 - -4);
    	a117 = a61;
    	a156 = ((((((a102 * a102) % 14999) * 2) % 61) + 106) - 1);
    	a16 = ((((((a187 * a187) % 14999) % 82) - -207) + 0) - -1);
    	a81 = (((((((a102 * a9) % 14999) - -1059) + -10297) * 1) % 93) - -177);
    	a120 = (((((((a120 * a187) % 14999) % 58) + 205) - 1) / 5) + 200);
    	a181 = (((((a102 * a102) % 14999) + -14974) + -21) - 4);
    	a61 = (a184 + 7);
    	a102 = ((((((a102 * a81) % 14999) % 58) - -255) + -1) * 1);
    	a130 = (a26 - -1);
    	a9 = ((((((a187 * a187) % 14999) + 10983) * 1) % 31) - -192);
    	a184 = (a147 + -6); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((a61 == 10 && ((a9 <=  159 && a159 <=  150) && a81 <=  84)) && (a130 == 4 && (((input == 4) &&  cf==1 ) && a75 == 8))) && (a122 % 2==0))) {
    	a60 += (a60 + 20) > a60 ? 4 : 0;
    	cf = 0;
    	a45 = (a184 - -2);
    	a100 = (((((((a100 * a58) % 14999) + 13934) - 27777) - 710) % 36) + 6);
    	a157 = (a83 + -4); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((a159 <=  150 && ((a156 <=  44 && a156 <=  44) && a16 <=  125)) && (a156 <=  44 && (((input == 2) &&  cf==1 ) && a83 == 10)))) {
    	a164 += (a164 + 20) > a164 ? 2 : 0;
    	a112 -= (a112 - 20) < a112 ? 4 : 0;
    	a186 += (a186 + 20) > a186 ? 2 : 0;
    	a43 -= (a43 - 20) < a43 ? 3 : 0;
    	cf = 0;
    	a27 = a117;
    	a45 = (a147 - 3);
    	a117 = (a66 + 2);
    	a187 = ((((((a187 * a81) % 14999) % 107) - 67) - 2) - -1);
    	a120 = ((((((((a120 * a78) % 14999) * 2) % 58) - -204) * 5) % 58) + 196);
    	a159 = ((((((a159 * a9) % 14999) - -7789) + 3321) % 32) - -184);
    	a184 = (a27 + -4);
    	a147 = ((a27 * a27) - 70);
    	a158 = ((((((a9 * a102) % 14999) / 5) + 7913) * 10) / 9);
    	a83 = ((a75 - a147) + 14);
    	a26 = (a66 - 3);
    	a100 = (((((((a100 * a81) % 14999) + -11911) % 36) - -6) + 7775) - 7773);
    	a81 = (((((((a156 * a187) % 14999) % 93) + 179) + 1) + 10796) - 10796);
    	a75 = (a66 - -2);
    	a156 = ((((((a156 * a159) % 14999) * 2) % 15022) - 14977) * 1);
    	a9 = (((((((a187 * a58) % 14999) - -12798) + 642) - -1194) % 31) - -191);
    	a102 = ((((((a102 * a16) % 14999) % 58) + 255) - -6219) + -6219);
    	a61 = (a130 + 7);
    	a130 = ((a26 - a27) + 10);
    	a16 = ((((((a16 * a58) % 14999) % 82) - -208) - 1) + 0);
    	a58 = (((a58 - 0) + 0) - 0); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((a75 == 8 && a26 == 3) && ((((( cf==1  && (input == 5)) && a156 <=  44) && a147 == 10) && a120 <=  146) && a75 == 8))) {
    	a43 += (a43 + 20) > a43 ? 1 : 0;
    	cf = 0;
    	a45 = ((a147 - a61) + 8);
    	a184 = (a75 - 3);
    	a81 = (((((((a81 * a9) % 14999) * 2) % 93) + 177) / 5) - -163);
    	a195 = (a27 - 4);
    	a61 = ((a147 - a130) - -5);
    	a100 = ((((((((a100 * a187) % 14999) - 8239) % 36) + 6) * 5) % 36) + 7);
    	a156 = ((((((a156 * a100) % 14999) % 61) + 105) + 0) + 1);
    	a83 = (a66 - -4);
    	a159 = ((((((a159 * a58) % 14999) - -9153) - 13681) % 32) + 182);
    	a16 = ((((((((a102 * a78) % 14999) / 5) % 82) - -207) * 5) % 82) - -181);
    	a26 = (a45 + -4);
    	a120 = (((((((a120 * a159) % 14999) % 58) + 205) * 1) / 5) - -148);
    	a9 = ((((((a9 * a102) % 14999) + -8681) % 31) - -192) - 1);
    	a58 = (((((((a58 * a159) % 14999) % 65) - -76) + -9121) - 18780) + 27901);
    	a75 = ((a147 * a45) + -71);
    	a117 = ((a184 * a130) + -10);
    	a27 = (a26 - -5);
    	a130 = ((a184 - a147) - -10);
    	a187 = (((((((a187 * a16) % 14999) % 107) + -67) * 5) % 107) + -68);
    	a102 = (((((((a102 * a159) % 14999) % 58) + 255) * 5) % 58) - -203);
    	a147 = (a45 + 3); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
}
 void calculate_outputm6(int input) {
    if(((a27 == 8 && (a27 == 8 && (a120 <=  146 && ( cf==1  && a78 <=  -40)))) && (a83 == 10 && (a58 <=  11 && a159 <=  150)))) {
    	calculate_outputm58(input);
    } 
}
 void calculate_outputm75(int input) {
    if(((((((input == 1) &&  cf==1 ) && ((84 < a81) && (272 >= a81))) && a61 == 11) && (((125 < a16) && (290 >= a16)) && (((11 < a58) && (142 >= a58)) && (((-176 < a187) && (39 >= a187)) && a184 == 5)))) && a50 == 1938)) {
    	a197 -= (a197 - 20) < a197 ? 4 : 0;
    	cf = 0;
    	a100 = ((((((a100 * a156) / 5) - -1328) * 5) * -1) / 10);
    	a172 = ((a39 / a83) - -2);
    	a66 = (a75 + -6); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((((((11 < a58) && (142 >= a58)) && a27 == 9) && a26 == 4) && (((( cf==1  && (input == 3)) && a83 == 11) && ((-176 < a187) && (39 >= a187))) && ((125 < a16) && (290 >= a16)))) && a138 >= 5)) {
    	a60 += (a60 + 20) > a60 ? 3 : 0;
    	cf = 0;
    	a9 = ((((((a102 * a81) % 14999) - -11742) / -5) * 10) / 9);
    	a120 = (((((a120 * a9) % 14999) + -14991) / 5) * 5);
    	a156 = (((((a58 * a16) % 14999) + -20609) / 5) + -2511);
    	a66 = (a83 - 3);
    	a130 = (a61 + -7);
    	a184 = (a83 + -7);
    	a117 = (a83 - 2);
    	a195 = ((a83 + a75) - 11);
    	a26 = ((a147 / a147) - -2);
    	a100 = ((((a100 * a81) - 12200) - 4236) + -4493);
    	a75 = ((a61 * a27) - 91);
    	a27 = ((a83 + a26) + -6);
    	a61 = (a83 + -1);
    	a81 = (((((a81 * a156) % 14999) - 14921) - 9) - 54); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((((159 < a9) && (223 >= a9)) && (((146 < a120) && (263 >= a120)) && ((44 < a156) && (168 >= a156)))) && ((44 < a156) && (168 >= a156))) && ((( cf==1  && (input == 5)) && a83 == 11) && a184 == 5))) {
    	a122 += (a122 + 20) > a122 ? 2 : 0;
    	a191 -= (a191 - 20) < a191 ? 2 : 0;
    	cf = 0;
    	a72 = ((a26 - a27) + 13);
    	a45 = ((a26 + a75) - 11);
    	a159 = ((((((((a81 * a58) % 14999) % 32) + 177) * 9) / 10) / 5) - -164); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if(((((((146 < a120) && (263 >= a120)) && ((125 < a16) && (290 >= a16))) && a147 == 11) && (a147 == 11 && (a184 == 5 && (a147 == 11 && ( cf==1  && (input == 4)))))) && a33 <= -7)) {
    	a33 += (a33 + 20) > a33 ? 4 : 0;
    	cf = 0;
    	a66 = ((a26 - a147) - -10);
    	a16 = (((((a16 * a187) % 14999) + 10322) + -2056) + -23187);
    	a58 = (((((a58 * a187) - 4723) + -422) % 15005) - 14993);
    	a75 = (a45 - -7);
    	a117 = (a184 - -4);
    	a27 = (a39 + -3);
    	a100 = (((((a100 * a102) - 20134) - -11319) - -3882) + -10879);
    	a81 = (((((a81 * a187) % 14999) + -14934) / 5) - 17389);
    	a184 = (a147 - 7);
    	a102 = ((((((a102 * a187) % 14999) - 14809) / 5) + 15151) - 37642);
    	a172 = (a39 - 5);
    	a61 = (a130 - -5); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if((((((146 < a120) && (263 >= a120)) && ((input == 2) &&  cf==1 )) && a26 == 4) && (((44 < a156) && (168 >= a156)) && (a27 == 9 && (((125 < a16) && (290 >= a16)) && ((84 < a81) && (272 >= a81))))))) {
    	a138 -= (a138 - 20) < a138 ? 1 : 0;
    	cf = 0;
    	a26 = (a39 + -6);
    	a117 = (a26 - -6);
    	a100 = ((((a100 * a156) + 8992) + 1756) + 5608);
    	a184 = (a27 - 3);
    	a156 = ((((((((a187 * a16) % 14999) + -1023) % 104) - -274) + -1448) * -2) / 10);
    	a9 = ((((((a9 * a187) % 14999) + -627) - -660) % 34) + 257);
    	a130 = (a61 - 5);
    	a27 = (a26 + 5);
    	a148 = (((((a81 * a120) % 14999) + 7679) - -4886) / 5);
    	a159 = ((((((a187 * a187) % 14999) + 3933) % 38) + 254) - 0);
    	a16 = (((((((a16 * a102) % 14999) - 27302) % 54) + 379) - -6696) + -6718);
    	a83 = (a39 - -1);
    	a75 = (a45 - -9);
    	a58 = ((((((a187 * a187) % 14999) + -12302) - -18034) % 69) + 211);
    	a147 = (a184 - -6);
    	a61 = (a39 - -1);
    	a120 = ((((((a159 * a187) % 14999) * 2) % 101) - -365) + -1);
    	a81 = ((((((a159 * a102) % 14999) % 41) - -295) - 23918) - -23910);
    	a102 = ((((((a102 * a58) % 14999) + 2160) % 83) + 320) * 1);
    	a167 = (a39 + -2);
    	a187 = (((((a187 * 5) % 99) - -139) / 5) - -140); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
}
 void calculate_outputm9(int input) {
    if(((((196 < a102) && (314 >= a102)) && ((a39 == 11 &&  cf==1 ) && a130 == 5)) && (a75 == 9 && (a75 == 9 && (a147 == 11 && ((196 < a102) && (314 >= a102))))))) {
    	calculate_outputm75(input);
    } 
}
 void calculate_outputm78(int input) {
    if((((((44 < a156) && (168 >= a156)) && ((a184 == 5 && ((a26 == 4 && ((11 < a58) && (142 >= a58))) && a61 == 11)) && a117 == 10)) && ( cf==1  && (input == 4))) && a25 == 3052)) {
    	a64 -= (a64 - 20) < a64 ? 1 : 0;
    	cf = 0;
    	a100 = (((((a100 * a58) + -16464) * 1) * 10) / 9);
    	a66 = (a147 + -7);
    	a121 = ((a61 / a66) + 5); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if(((a61 == 11 && (((84 < a81) && (272 >= a81)) && a61 == 11)) && ((a117 == 10 && (a75 == 9 && ( cf==1  && (input == 5)))) && a117 == 10))) {
    	a197 -= (a197 - 20) < a197 ? 2 : 0;
    	cf = 0;
    	a159 = (((((((a156 * a81) % 14999) + -2151) % 32) - -183) / 5) - -153);
    	a72 = (a26 - -4); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if((((((44 < a156) && (168 >= a156)) && a147 == 11) && a75 == 9) && (((146 < a120) && (263 >= a120)) && (((84 < a81) && (272 >= a81)) && (((196 < a102) && (314 >= a102)) && ( cf==1  && (input == 3))))))) {
    	a76 += (a76 + 20) > a76 ? 2 : 0;
    	cf = 0;
    	a45 = ((a61 - a130) + -5);
    	a159 = (((((a102 * a156) % 14999) + 4883) / 5) - 5532);
    	a39 = a147; 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((((((146 < a120) && (263 >= a120)) && (a184 == 5 && a147 == 11)) && ((196 < a102) && (314 >= a102))) && ((a75 == 9 && ((input == 1) &&  cf==1 )) && ((196 < a102) && (314 >= a102)))) && (a135 % 2==0))) {
    	a68 += (a68 + 20) > a68 ? 3 : 0;
    	cf = 0;
    	a7 = (((((((a58 * a120) % 14999) - 24462) % 41) + 123) - -21490) - 21513);
    	a100 = ((((((a100 * a120) % 49) + 94) + 1) + 12574) + -12574);
    	a176 = (a130 + -3); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if((((((146 < a120) && (263 >= a120)) && (a130 == 5 && ((input == 2) &&  cf==1 ))) && ((((11 < a58) && (142 >= a58)) && (a61 == 11 && a83 == 11)) && a117 == 10)) && a182 >= -2)) {
    	a89 += (a89 + 20) > a89 ? 1 : 0;
    	cf = 0;
    	a0 = (a72 + 5);
    	a61 = (a0 + 1);
    	a7 = (((((a100 * a187) - 10203) - 3883) % 54) + 241);
    	a100 = ((((((a100 * a58) % 49) - -94) / 5) / 5) - -114);
    	a147 = (a184 - -7);
    	a9 = (((((((a9 * a16) % 14999) / 5) % 34) + 227) / 5) - -212);
    	a26 = ((a61 + a45) - 9);
    	a117 = a83;
    	a156 = ((((((((a156 * a120) % 14999) % 104) - -233) + 26) * 5) % 104) + 211);
    	a102 = ((((((a102 * a81) % 14999) % 83) - -373) - 19491) + 19491);
    	a81 = ((((((a9 * a9) % 14999) + -10857) % 41) - -313) + 2);
    	a83 = (a130 + 7);
    	a130 = (a27 - 3);
    	a120 = (((((((a120 * a9) % 14999) - -5584) + 7765) * 1) % 101) + 286); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
}
 void calculate_outputm79(int input) {
    if(((a61 == 11 && (a75 == 9 && (((((input == 2) &&  cf==1 ) && a147 == 11) && ((146 < a120) && (263 >= a120))) && ((146 < a120) && (263 >= a120))))) && ((159 < a9) && (223 >= a9)))) {
    	a76 += (a76 + 20) > a76 ? 2 : 0;
    	cf = 0;
    	 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
    if(((((((input == 1) &&  cf==1 ) && a27 == 9) && a184 == 5) && (a75 == 9 && ((a75 == 9 && ((125 < a16) && (290 >= a16))) && a184 == 5))) && a151 >= 7)) {
    	a164 -= (a164 - 20) < a164 ? 2 : 0;
    	cf = 0;
    	a45 = (a83 - 5);
    	a157 = (a184 + 2); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((a26 == 4 && (((150 < a159) && (216 >= a159)) && ((-176 < a187) && (39 >= a187)))) && ((a130 == 5 && (((input == 4) &&  cf==1 ) && ((196 < a102) && (314 >= a102)))) && a130 == 5)) && (a99 % 2==0))) {
    	cf = 0;
    	a45 = ((a61 - a27) - -4);
    	a157 = ((a26 / a184) - -9); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((((44 < a156) && (168 >= a156)) && ((((159 < a9) && (223 >= a9)) && ((125 < a16) && (290 >= a16))) && a75 == 9)) && ((-176 < a187) && (39 >= a187))) && (((input == 5) &&  cf==1 ) && a130 == 5))) {
    	a177 += (a177 + 20) > a177 ? 6 : 0;
    	a64 += (a64 + 20) > a64 ? 2 : 0;
    	a99 += (a99 + 20) > a99 ? 2 : 0;
    	cf = 0;
    	a58 = (((((a187 * a159) % 14999) / 5) / 5) - 12483);
    	a100 = ((((a100 * a120) + -19719) + -2433) - 160);
    	a83 = (a130 + 5);
    	a172 = a130;
    	a26 = ((a75 * a147) + -96);
    	a16 = (((((a16 * a187) % 14999) + -14960) + -9) + -32);
    	a61 = (a130 - -5);
    	a66 = (a72 - 5);
    	a102 = (((((a102 * a120) % 14999) - -9553) - 15334) - 14625);
    	a117 = (a45 - -7);
    	a184 = (a61 + -6);
    	a156 = (((((a156 * a58) % 14999) + -12816) / 5) - 18505);
    	a75 = ((a130 - a130) + 8);
    	a9 = ((((((a9 * a100) % 14999) + -1803) * 1) - -3279) + -8823);
    	a27 = ((a130 * a130) - 17);
    	a120 = ((((((a159 * a81) % 14999) / 5) - 17858) * 10) / 9);
    	a187 = (((((((a58 * a58) % 14999) % 14912) + -15087) * 1) + 17077) - 17078);
    	a81 = ((((((a58 * a58) % 14999) + -14935) / 5) - -1633) + -18267);
    	a147 = ((a83 - a130) - -5);
    	a159 = (((((a159 * a9) % 14999) / 5) - -12975) * -1);
    	a130 = (a83 - 6); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((((((11 < a58) && (142 >= a58)) && ((input == 3) &&  cf==1 )) && ((150 < a159) && (216 >= a159))) && ((125 < a16) && (290 >= a16))) && ((((-176 < a187) && (39 >= a187)) && ((150 < a159) && (216 >= a159))) && ((44 < a156) && (168 >= a156)))) && a64 >= 5)) {
    	a197 -= (a197 - 20) < a197 ? 1 : 0;
    	cf = 0;
    	a100 = ((((((a100 * a156) % 49) + 93) + -15023) + 2403) + 12621);
    	a7 = (((((a81 * a100) % 14999) + -5232) - -10525) * 1);
    	a130 = ((a75 / a27) + 5);
    	a102 = (((((((a102 * a16) % 14999) % 83) + 331) - 26733) * 1) + 26731);
    	a28 = ((((((a100 * a81) % 14999) - -7397) * 1) * 10) / 9);
    	a184 = (a75 + -3);
    	a159 = (((((((a159 * a156) % 14999) / 5) % 38) + 251) + -21523) - -21513);
    	a61 = (a26 + 8);
    	a83 = (a45 + 10);
    	a187 = (((((a187 * a100) / 5) / 5) % 99) - -139);
    	a117 = ((a147 + a184) - 6);
    	a26 = (a184 - 1);
    	a75 = (a61 - 2); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
}
 void calculate_outputm10(int input) {
    if(((((125 < a16) && (290 >= a16)) && ((a26 == 4 && a61 == 11) && ((11 < a58) && (142 >= a58)))) && (a147 == 11 && (( cf==1  && a72 == 6) && a27 == 9)))) {
    	calculate_outputm78(input);
    } 
    if(((((159 < a9) && (223 >= a9)) && (((a27 == 9 && (a72 == 8 &&  cf==1 )) && a184 == 5) && ((150 < a159) && (216 >= a159)))) && (a26 == 4 && ((196 < a102) && (314 >= a102))))) {
    	calculate_outputm79(input);
    } 
}
 void calculate_outputm86(int input) {
    if(((((44 < a156) && (168 >= a156)) && ((84 < a81) && (272 >= a81))) && ((((((input == 2) &&  cf==1 ) && ((11 < a58) && (142 >= a58))) && a184 == 5) && a61 == 11) && a130 == 5))) {
    	cf = 0;
    	a156 = ((((((a156 * a120) % 14999) + -16092) + 204) - -2536) - 2615);
    	a187 = ((((((a156 * a156) % 14999) * 2) % 14912) - 15087) - 1);
    	a83 = ((a26 / a27) + 10);
    	a120 = (((((a120 * a181) % 14999) - 14921) + -37) + -25);
    	a102 = ((((((a102 * a187) % 14999) + 3157) * 2) * 1) - 6207);
    	a147 = (a130 + 5);
    	a27 = (a83 - 2);
    	a81 = (((((a187 * a187) % 14999) + -24158) + 34732) - 38605);
    	a61 = (a26 + 6);
    	a117 = (a130 + 4);
    	a78 = ((((((a16 * a58) % 14999) + 13237) - 40823) - -16214) - 4975);
    	a66 = (a130 + 2);
    	a100 = ((((a100 * a9) + -11474) * 1) * 1);
    	a75 = ((a130 + a45) - 1);
    	a58 = (((((a159 * a102) % 14999) + 4755) + -19755) - 2);
    	a16 = ((((((a102 * a81) % 14999) - -4701) * 1) + 3979) + -23657);
    	a9 = ((((((a81 * a159) % 14999) + -14898) - 75) + 9463) + -9336);
    	a26 = ((a130 * a130) - 22);
    	a184 = ((a75 / a117) + 4);
    	a159 = (((((a159 * a156) % 14999) + -14991) * 1) + -8);
    	a130 = (a61 + -6); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((((-176 < a187) && (39 >= a187)) && ((a27 == 9 && (((input == 5) &&  cf==1 ) && ((196 < a102) && (314 >= a102)))) && a26 == 4)) && (a117 == 10 && ((84 < a81) && (272 >= a81))))) {
    	a164 -= (a164 - 20) < a164 ? 2 : 0;
    	cf = 0;
    	a187 = ((((a58 * a58) * 1) + -26906) * 1);
    	a102 = (((((a16 * a16) % 14999) + -18600) * 1) / 5);
    	a75 = (a45 + 4);
    	a172 = (a27 + -4);
    	a9 = (((((a9 * a187) % 14999) + -2105) / 5) + -18576);
    	a156 = (((((a156 * a102) % 14999) / 5) + -14254) / 5);
    	a66 = (a27 - 6);
    	a100 = (((((a100 * a58) - 11560) * 1) - -15890) - 14726);
    	a120 = (((((a120 * a159) % 14999) - -2547) / 5) - 19226);
    	a81 = (((((a81 * a181) % 14999) / 5) + -14067) + -11028);
    	a184 = a26;
    	a130 = (a117 + -6);
    	a147 = (a75 - -2);
    	a27 = (a61 - 3);
    	a159 = (((((a187 * a187) % 14999) / 5) / 5) - 8299);
    	a117 = (a26 + 5);
    	a16 = (((((a9 * a58) % 14999) / 5) / 5) - 29333);
    	a83 = (a61 - 1);
    	a61 = (a26 + 6);
    	a58 = (((((a58 * a187) % 14999) + -12350) - 1757) / 5);
    	a26 = 3; 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((( cf==1  && (input == 3)) && a75 == 9) && ((150 < a159) && (216 >= a159))) && (((((44 < a156) && (168 >= a156)) && ((-176 < a187) && (39 >= a187))) && ((-176 < a187) && (39 >= a187))) && ((146 < a120) && (263 >= a120))))) {
    	a101 += (a101 + 20) > a101 ? 6 : 0;
    	a12 += (a12 + 20) > a12 ? 4 : 0;
    	a15 += (a15 + 20) > a15 ? 2 : 0;
    	a112 += (a112 + 20) > a112 ? 4 : 0;
    	cf = 0;
    	a39 = ((a75 / a45) - -9);
    	a159 = (((((a159 * a102) % 14999) + -17196) - -14277) - 18626);
    	a45 = (a26 + -3); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm12(int input) {
    if((((((a181 <=  162 &&  cf==1 ) && a147 == 11) && a83 == 11) && a130 == 5) && ((((146 < a120) && (263 >= a120)) && ((44 < a156) && (168 >= a156))) && a184 == 5))) {
    	calculate_outputm86(input);
    } 
}
 void calculate_outputm98(int input) {
    if(((((84 < a81) && (272 >= a81)) && (((11 < a58) && (142 >= a58)) && ( cf==1  && (input == 5)))) && (a130 == 5 && (((-176 < a187) && (39 >= a187)) && (((84 < a81) && (272 >= a81)) && ((159 < a9) && (223 >= a9))))))) {
    	cf = 0;
    	a102 = (((((a102 * a16) % 14999) - 14902) / 5) + -3977);
    	a147 = (a26 - -6);
    	a130 = (a45 + -2);
    	a187 = ((((((a16 * a81) % 14999) + -26510) - -16053) / 5) + -21817);
    	a172 = ((a26 - a75) + 10);
    	a75 = (a157 + -3);
    	a120 = (((((a120 * a81) % 14999) - 14368) - 8937) / 5);
    	a83 = (a117 + 1);
    	a61 = ((a26 - a130) + 10);
    	a184 = ((a26 * a26) - 12);
    	a100 = ((((a100 * a16) - 16398) - 2356) - 1060);
    	a27 = ((a45 * a61) - 52);
    	a81 = ((((((a81 * a16) % 14999) - 9888) - 5986) * 10) / 9);
    	a58 = (((((a58 * a187) % 14999) - 11923) - -33497) - 33373);
    	a66 = (a45 - 3);
    	a9 = ((((((a9 * a16) % 14999) + -22148) + -7784) - -25762) - 21769);
    	a26 = ((a147 + a184) - 11);
    	a16 = (((((a16 * a156) % 14999) - 14927) * 1) - 61); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
}
 void calculate_outputm100(int input) {
    if(((((159 < a9) && (223 >= a9)) && a61 == 11) && ((((84 < a81) && (272 >= a81)) && ((((input == 5) &&  cf==1 ) && a130 == 5) && ((11 < a58) && (142 >= a58)))) && a61 == 11))) {
    	a164 -= (a164 - 20) < a164 ? 3 : 0;
    	cf = 0;
    	a158 = (((((((a58 * a159) % 14999) % 74) - -183) + 5) - 15378) + 15354);
    	a45 = (a130 + 2);
    	a117 = (a184 - -5); 
    	 printf("%d\n", 19); fflush(stdout); 
    } 
    if((((((44 < a156) && (168 >= a156)) && ((a75 == 9 && ((196 < a102) && (314 >= a102))) && ((196 < a102) && (314 >= a102)))) && (a75 == 9 && (((input == 1) &&  cf==1 ) && ((146 < a120) && (263 >= a120))))) && a137 <= -1)) {
    	a138 -= (a138 - 20) < a138 ? 3 : 0;
    	cf = 0;
    	a81 = ((((((a81 * a159) % 14999) + 2783) / 5) % 41) + 274);
    	a148 = (((((((a187 * a120) % 14999) / 5) * 5) * 2) % 52) - 20);
    	a90 = (a157 + 1);
    	a100 = (((((a100 * a156) + 12417) * 10) / 9) + 7066);
    	a120 = ((((((a159 * a81) % 14999) + 13719) % 101) - -351) + -62);
    	a130 = (a61 - 5);
    	a156 = ((((((a81 * a58) % 14999) / 5) - 8959) % 104) - -290);
    	a184 = (a26 + 2);
    	a102 = ((((((((a102 * a159) % 14999) % 83) - -334) + -5238) / 5) * -4) / 10);
    	a27 = ((a75 + a75) + -8);
    	a9 = (((((((a9 * a58) % 14999) % 34) - -242) / 5) * 10) / 2);
    	a159 = (((((((a159 * a81) % 14999) % 38) + 248) - 6) + -5340) - -5315); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((a61 == 11 && (((159 < a9) && (223 >= a9)) && (a61 == 11 && ((159 < a9) && (223 >= a9))))) && ((( cf==1  && (input == 3)) && ((44 < a156) && (168 >= a156))) && a75 == 9))) {
    	a43 -= (a43 - 20) < a43 ? 1 : 0;
    	cf = 0;
    	a120 = ((((((a16 * a156) % 14999) - 25197) * 10) / 9) - 525);
    	a66 = ((a45 * a147) - 64);
    	a130 = ((a45 / a83) - -4);
    	a75 = ((a45 - a83) - -13);
    	a166 = ((a83 / a83) - -14);
    	a117 = ((a83 + a157) + -15);
    	a26 = (a61 + -8);
    	a58 = (((((a81 * a9) % 14999) + 9676) + -30312) * 1);
    	a102 = (((((a102 * a120) % 14999) - 14918) + -27) / 5);
    	a159 = (((((a159 * a120) % 14999) / 5) / 5) - 28742);
    	a27 = ((a117 / a130) - -6);
    	a147 = ((a117 / a157) + 10);
    	a100 = ((((a100 * a187) + 12710) + -30172) * 1);
    	a61 = (a45 - -4);
    	a16 = ((((((a120 * a120) % 14999) - 6916) + 2644) / 5) + -17198);
    	a184 = (a147 + -6);
    	a81 = (((((a81 * a58) % 14999) - 14941) - 50) + -6);
    	a156 = (((((a120 * a120) % 14999) - 14960) - 29) + -12);
    	a187 = ((((((a120 * a120) % 14999) % 14912) + -15087) / 5) + -2029);
    	a9 = ((((((a120 * a120) % 14999) / 5) - 1999) * 5) + -4856);
    	a83 = ((a157 + a130) - 7); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((((84 < a81) && (272 >= a81)) && ( cf==1  && (input == 4))) && (((196 < a102) && (314 >= a102)) && (a61 == 11 && ((((84 < a81) && (272 >= a81)) && a83 == 11) && a61 == 11)))) && (a131 % 2==0))) {
    	a43 -= (a43 - 20) < a43 ? 4 : 0;
    	cf = 0;
    	a157 = (a130 + 3); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((((11 < a58) && (142 >= a58)) && (((-176 < a187) && (39 >= a187)) && (a130 == 5 && (((input == 2) &&  cf==1 ) && ((125 < a16) && (290 >= a16)))))) && (a75 == 9 && ((196 < a102) && (314 >= a102))))) {
    	a137 += (a137 + 20) > a137 ? 4 : 0;
    	cf = 0;
    	a72 = (a157 + -7);
    	a117 = ((a184 + a75) - 4);
    	a45 = (a184 + -3);
    	a159 = ((((((a159 * a102) % 14999) % 38) + 224) * 1) + -7); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm14(int input) {
    if(((((((159 < a9) && (223 >= a9)) && (a27 == 9 && ( cf==1  && a157 == 11))) && a27 == 9) && a83 == 11) && (a130 == 5 && ((11 < a58) && (142 >= a58))))) {
    	calculate_outputm98(input);
    } 
    if(((((84 < a81) && (272 >= a81)) && (a157 == 13 &&  cf==1 )) && ((((84 < a81) && (272 >= a81)) && (a26 == 4 && (((150 < a159) && (216 >= a159)) && ((150 < a159) && (216 >= a159))))) && a184 == 5))) {
    	calculate_outputm100(input);
    } 
}
 void calculate_outputm102(int input) {
    if((((a83 == 11 && (a184 == 5 && ((125 < a16) && (290 >= a16)))) && a184 == 5) && (a75 == 9 && (((input == 5) &&  cf==1 ) && ((159 < a9) && (223 >= a9)))))) {
    	a137 += (a137 + 20) > a137 ? 4 : 0;
    	cf = 0;
    	a9 = (((((a120 * a120) % 14999) / 5) - -26478) - 35466);
    	a187 = ((((((a187 * a9) % 14999) % 14912) - 15087) - 2) + 0);
    	a66 = (a61 + -8);
    	a100 = ((((a100 * a58) + -19373) - 5295) + -733);
    	a102 = (((((a102 * a158) % 14999) + -24211) + 23080) - 25007);
    	a26 = (a130 + -2);
    	a147 = ((a27 * a45) - 53);
    	a159 = ((((((a159 * a187) % 14999) + -10856) * 1) - -38456) - 36602);
    	a184 = (a26 + 1);
    	a61 = a117;
    	a83 = (a75 - -1);
    	a172 = (a66 + 2);
    	a156 = ((((((a156 * a81) % 14999) - 16362) - 3265) + 29760) * -1);
    	a120 = (((((a120 * a9) % 14999) + -14981) + -19) * 1);
    	a81 = ((((((a9 * a9) % 14999) * 2) % 15042) - 14957) - 2);
    	a27 = ((a130 - a83) - -13);
    	a58 = ((((((a58 * a16) % 14999) + -18945) * 10) / 9) - 437);
    	a16 = ((((((a9 * a9) % 14999) + -14995) * 1) + 21552) + -21453);
    	a130 = ((a117 - a117) - -4);
    	a117 = a75;
    	a75 = 8; 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((((((input == 1) &&  cf==1 ) && ((84 < a81) && (272 >= a81))) && ((196 < a102) && (314 >= a102))) && (a27 == 9 && ((a75 == 9 && a27 == 9) && ((150 < a159) && (216 >= a159))))) && a106 <= -1)) {
    	a191 += (a191 + 20) > a191 ? 2 : 0;
    	cf = 0;
    	a130 = (a83 + -7);
    	a9 = (((((a81 * a120) % 14999) / 5) - 18594) + 15474);
    	a81 = (((((a120 * a158) % 14999) + -25941) - 2707) + -52);
    	a27 = ((a147 + a130) - 7);
    	a172 = (a184 + 2);
    	a61 = ((a184 + a75) + -4);
    	a100 = (((((a100 * a102) * 2) - 2952) / 5) + -10600);
    	a102 = ((((((a9 * a156) % 14999) - 9813) - -11891) + 5703) + -22780);
    	a117 = ((a130 * a147) - 35);
    	a58 = (((((a58 * a16) % 14999) - 13909) + -10354) / 5);
    	a187 = (((((((a187 * a120) % 14999) % 14912) + -15087) - 2) / 5) - 5196);
    	a66 = (a147 - 8);
    	a159 = ((((((a159 * a158) % 14999) - 23302) + 28053) - -4371) * -1);
    	a184 = (a117 + -5);
    	a16 = (((((a16 * a158) % 14999) / 5) - 17281) + -9942); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((((( cf==1  && (input == 4)) && ((196 < a102) && (314 >= a102))) && ((11 < a58) && (142 >= a58))) && (a184 == 5 && ((a184 == 5 && a26 == 4) && a147 == 11))) && a152 >= 1)) {
    	a68 += (a68 + 20) > a68 ? 4 : 0;
    	cf = 0;
    	a166 = (a184 + 7);
    	a83 = (a166 + -2);
    	a100 = ((((a100 * a16) - 17121) - 3667) - 191);
    	a159 = (((((a158 * a102) % 14999) - 24203) * 1) + -3732);
    	a27 = (a166 + -4);
    	a156 = ((((((a156 * a159) % 14999) - 14983) - -14200) * 1) - 14176);
    	a66 = (a75 - 7);
    	a117 = (a184 - -4);
    	a184 = a26;
    	a61 = (a45 + 3);
    	a75 = ((a61 / a147) - -8);
    	a81 = ((((((a81 * a187) % 14999) - -3022) + -17999) - -17588) + -17568); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((( cf==1  && (input == 3)) && a117 == 10) && (a117 == 10 && (a117 == 10 && ((a61 == 11 && a117 == 10) && a147 == 11))))) {
    	a164 -= (a164 - 20) < a164 ? 3 : 0;
    	cf = 0;
    	a187 = (((((a158 * a120) % 14999) - 29588) + -113) - 91);
    	a130 = ((a117 + a117) - 16);
    	a16 = (((((a81 * a81) % 14999) / 5) + -22869) - -7793);
    	a81 = ((((((a81 * a187) % 14999) - 4398) * 10) / 9) * 1);
    	a159 = ((((((a159 * a9) % 14999) + -24890) * 1) + 13126) - 15880);
    	a75 = (a130 - -4);
    	a9 = (((((a120 * a120) % 14999) + 768) / -5) / 5);
    	a58 = (((((a58 * a102) % 14999) - 23264) - 5284) / 5);
    	a172 = ((a26 - a45) + 8);
    	a102 = (((((a16 * a100) % 14999) - 14897) - -20479) + -20568);
    	a184 = ((a83 * a26) + -40);
    	a156 = (((((a156 * a187) % 14999) - 7825) * 1) - 6792);
    	a27 = ((a75 - a75) - -8);
    	a147 = ((a172 - a117) - -15);
    	a66 = (a26 + -1);
    	a100 = ((((a100 * a120) / 5) - 23690) + -2647);
    	a26 = (a61 + -8);
    	a61 = (a130 + 6);
    	a83 = (a130 - -6);
    	a117 = (a130 + 5);
    	a120 = (((((a120 * a187) % 14999) / 5) / 5) - 20620); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((((196 < a102) && (314 >= a102)) && ((44 < a156) && (168 >= a156))) && a26 == 4) && ((a147 == 11 && (((196 < a102) && (314 >= a102)) && ( cf==1  && (input == 2)))) && ((150 < a159) && (216 >= a159))))) {
    	a97 -= (a97 - 20) < a97 ? 1 : 0;
    	cf = 0;
    	a45 = (a184 - 3);
    	a72 = (a130 + 3); 
    	 printf("%d\n", 21); fflush(stdout); 
    } 
}
 void calculate_outputm104(int input) {
    if(((((-176 < a187) && (39 >= a187)) && (((84 < a81) && (272 >= a81)) && ( cf==1  && (input == 2)))) && (((((146 < a120) && (263 >= a120)) && ((146 < a120) && (263 >= a120))) && ((159 < a9) && (223 >= a9))) && a61 == 11))) {
    	a42 += (a42 + 20) > a42 ? 2 : 0;
    	cf = 0;
    	a187 = (((((((a187 * a16) % 14999) - 5145) + 13296) - 9618) % 14912) - 15087);
    	a61 = ((a130 / a117) + 10);
    	a159 = (((((a159 * a158) % 14999) + -25098) * 1) + -1084);
    	a196 = ((a184 - a147) - -17);
    	a66 = (a75 + -3);
    	a184 = (a75 + -5);
    	a27 = (a26 + 4);
    	a81 = ((((((a81 * a120) % 14999) + -23902) * 10) / 9) + -777);
    	a147 = ((a83 + a83) + -12);
    	a130 = (a27 - 4);
    	a102 = (((((a102 * a9) % 14999) + -26078) + -2477) - 744);
    	a83 = (a26 + 6);
    	a100 = ((((a100 * a120) - 14122) + -4738) * 1);
    	a16 = (((((a187 * a58) % 14999) + 13027) - 23271) + -4649);
    	a9 = (((((a58 * a156) % 14999) + -14874) * 1) + -88);
    	a120 = (((((a120 * a156) % 14999) - 14919) + -48) + -20);
    	a75 = ((a45 + a45) - 6);
    	a26 = (a45 - 4); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((a75 == 9 && ((((125 < a16) && (290 >= a16)) && a147 == 11) && ((84 < a81) && (272 >= a81)))) && ((((159 < a9) && (223 >= a9)) && ((input == 3) &&  cf==1 )) && a83 == 11))) {
    	a112 += (a112 + 20) > a112 ? 3 : 0;
    	cf = 0;
    	a156 = (((((a81 * a120) % 14999) + -25716) + 33301) + -23378);
    	a117 = (a61 + -2);
    	a58 = (((((a16 * a158) % 14999) - 27919) - 57) + -1839); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((a27 == 9 && (a130 == 5 && (((196 < a102) && (314 >= a102)) && ((150 < a159) && (216 >= a159))))) && (((125 < a16) && (290 >= a16)) && (((input == 5) &&  cf==1 ) && a26 == 4)))) {
    	a197 += (a197 + 20) > a197 ? 1 : 0;
    	cf = 0;
    	a58 = (((((((a120 * a158) % 14999) % 65) - -16) - 15879) / 5) - -3281);
    	a159 = ((((((a159 * a58) % 14999) + -20761) * 10) / 9) * 1);
    	a45 = (a83 + -10);
    	a39 = (a26 - -7);
    	a156 = (((((((a102 * a187) % 14999) % 61) + 105) - -2) / 5) - -121);
    	a117 = (a83 + -1); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
}
 void calculate_outputm15(int input) {
    if(((((((((114 < a158) && (263 >= a158)) &&  cf==1 ) && ((-176 < a187) && (39 >= a187))) && a147 == 11) && ((44 < a156) && (168 >= a156))) && ((11 < a58) && (142 >= a58))) && (a27 == 9 && a147 == 11))) {
    	calculate_outputm102(input);
    } 
    if((((a61 == 11 && ((a83 == 11 && (424 < a158 &&  cf==1 )) && ((84 < a81) && (272 >= a81)))) && a130 == 5) && (a130 == 5 && a147 == 11))) {
    	calculate_outputm104(input);
    } 
}
 void calculate_outputm105(int input) {
    if(((a75 == 9 && (((146 < a120) && (263 >= a120)) && ((44 < a156) && (168 >= a156)))) && (((84 < a81) && (272 >= a81)) && ((( cf==1  && (input == 5)) && a61 == 11) && a130 == 5)))) {
    	a67 += (a67 + 20) > a67 ? 4 : 0;
    	cf = 0;
    	a159 = (((((a16 * a16) % 14999) / 5) / 5) + -15696);
    	a26 = ((a117 + a195) - 11);
    	a117 = (a26 - -6);
    	a156 = (((((a159 * a159) % 14999) + -14956) * 1) + -38);
    	a16 = (((((a81 * a81) % 14999) + -17589) - 5696) + -2161);
    	a172 = ((a147 - a27) + 3);
    	a102 = ((((((a102 * a58) % 14999) / 5) - -17769) * 1) * -1);
    	a187 = ((((((a187 * a156) % 14999) % 14912) + -15087) - 1) - 0);
    	a9 = ((((((a9 * a159) % 14999) - 12640) * 1) / 5) + -13439);
    	a120 = ((((((a159 * a159) % 14999) - 6833) / 5) / 5) - 6933);
    	a66 = (a147 - a45);
    	a27 = (a26 + a130);
    	a81 = (((((a81 * a120) % 14999) + -3521) + -10503) - 976);
    	a100 = (((((a100 * a58) + 7270) * 10) / -9) + -11944);
    	a61 = (a83 - 1);
    	a147 = (a184 + 5);
    	a130 = (a26 + 1);
    	a58 = ((((((a159 * a159) % 14999) - -3231) * 1) - -5613) - 23834);
    	a184 = (a83 - 7);
    	a83 = ((a195 + a75) + -3);
    	a75 = (a26 + 5); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((a117 == 10 && (a26 == 4 && ((-176 < a187) && (39 >= a187)))) && a83 == 11) && (((150 < a159) && (216 >= a159)) && (((input == 3) &&  cf==1 ) && ((159 < a9) && (223 >= a9)))))) {
    	a151 += (a151 + 20) > a151 ? 2 : 0;
    	a25 += (a25 + 20) > a25 ? 4 : 0;
    	a34 += (a34 + 20) > a34 ? 2 : 0;
    	cf = 0;
    	a16 = (((((a156 * a159) % 14999) / 5) + 15800) / -5);
    	a102 = ((((((a16 * a9) % 14999) * 2) % 15098) - 14901) / 5);
    	a66 = (a27 - 2);
    	a100 = ((((a100 * a58) - 10613) / 5) + -24808);
    	a147 = ((a45 - a75) - -11);
    	a187 = (((((a187 * a58) % 14912) + -15087) + -1) - 1);
    	a184 = (a117 - 6);
    	a156 = (((((a16 * a16) % 14999) * 2) / 5) + -11645);
    	a130 = a195;
    	a61 = (a66 + 3);
    	a9 = (((((a9 * a102) % 14999) + 1063) - 15929) * 1);
    	a78 = (((((((a100 * a81) % 14999) + 25594) * 1) + -4883) * -1) / 10);
    	a120 = (((((a120 * a102) % 14999) + -10388) - 4546) - 29);
    	a81 = ((((((a81 * a16) % 14999) * 2) % 15042) - 14957) - 1);
    	a58 = (((((((a16 * a16) % 14999) * 2) - 2) + 3) % 15005) - 14993);
    	a26 = ((a130 * a75) + -33);
    	a117 = a75;
    	a159 = ((((((a159 * a16) % 14999) - 14994) - 6) - -26447) + -26423);
    	a27 = (a83 - a26);
    	a83 = (a75 - -1);
    	a75 = ((a130 - a130) - -8); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((a27 == 9 && ( cf==1  && (input == 2))) && a61 == 11) && (((125 < a16) && (290 >= a16)) && (((196 < a102) && (314 >= a102)) && (a184 == 5 && ((-176 < a187) && (39 >= a187))))))) {
    	a197 -= (a197 - 20) < a197 ? 3 : 0;
    	cf = 0;
    	a26 = (a117 - 7);
    	a75 = (a26 - -5);
    	a81 = ((((((a81 * a9) % 14999) + -26296) + 40609) - -46) * -1);
    	a187 = ((((((a187 * a16) % 14999) % 14912) - 15087) + -1) - 1);
    	a184 = ((a75 * a26) + -20);
    	a66 = ((a195 * a83) - 38);
    	a130 = (a45 - 4);
    	a100 = ((((a100 * a58) + -10807) - -21326) + -30795);
    	a16 = ((((((a81 * a120) % 14999) + 7820) + -21702) * 1) - 992);
    	a58 = ((((((a81 * a120) % 14999) / 5) + -19835) * 10) / 9);
    	a61 = (a130 + 6);
    	a159 = (((((a159 * a156) % 14999) + -18322) + -7642) * 1);
    	a83 = ((a45 * a45) + -54);
    	a102 = ((((((a102 * a120) % 14999) - 25095) * 10) / 9) + -238);
    	a156 = (((((a120 * a120) % 14999) + 4991) - 27858) - 4122);
    	a147 = (a27 + 1);
    	a117 = (a26 + 6);
    	a9 = ((((((a9 * a100) % 14999) - 10122) * 10) / 9) + -1105);
    	a196 = (a27 + 2);
    	a27 = ((a75 / a45) - -7);
    	a120 = (((((a120 * a159) % 14999) + -14930) - 16) - 14); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm108(int input) {
    if(((((a75 == 9 && (a130 == 5 && ((input == 1) &&  cf==1 ))) && ((125 < a16) && (290 >= a16))) && (a75 == 9 && (a117 == 10 && ((-176 < a187) && (39 >= a187))))) && a42 <= -1)) {
    	a89 -= (a89 - 20) < a89 ? 2 : 0;
    	cf = 0;
    	a117 = (a26 + 5);
    	a100 = ((((a100 * a120) + -21724) * 1) + -38);
    	a196 = (a45 - -4);
    	a81 = ((((((a81 * a102) % 14999) - -9993) * 1) / 5) + -28245);
    	a120 = (((((((a120 * a156) % 14999) * 2) - 2) + 0) % 15073) - 14926);
    	a27 = ((a195 * a184) + -32);
    	a147 = (a45 + 2);
    	a184 = (a130 + -1);
    	a66 = (a83 + -5);
    	a61 = (a75 - -1);
    	a130 = (a75 + -5);
    	a83 = (a75 - -1); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((a147 == 11 && (((146 < a120) && (263 >= a120)) && (((84 < a81) && (272 >= a81)) && a184 == 5))) && (((150 < a159) && (216 >= a159)) && (a27 == 9 && ((input == 3) &&  cf==1 ))))) {
    	a50 += (a50 + 20) > a50 ? 4 : 0;
    	cf = 0;
    	a83 = (a45 + 4);
    	a27 = (a83 + -2);
    	a180 = (((((a58 * a159) % 14999) - 3706) - -11499) * 1);
    	a58 = (((((((26 * 69) / 10) * 9) / 10) / 5) * 45) / 10);
    	a187 = ((((((87 * 10) / 9) * 9) / 10) * 9) / 10);
    	a148 = ((((((a16 * a102) % 14999) - 17608) + 1736) % 64) + 111);
    	a147 = (a75 + 3);
    	a26 = ((a27 * a117) - 95);
    	a100 = ((((a100 * a9) / 5) * 5) + 7997);
    	a117 = (a184 + 6);
    	a130 = ((a147 / a45) + 4);
    	a9 = (((((((a9 * a102) % 14999) % 31) + 188) + 2) + 22394) - 22414);
    	a159 = (((((((a159 * a120) % 14999) / 5) % 32) + 168) - -3254) - 3262);
    	a75 = (a83 + -2);
    	a156 = ((((85 - -17246) + -17020) + -715) + 758);
    	a102 = ((((86 - 10022) + 10351) - 13098) + 13151);
    	a16 = (((((((a120 * a120) % 14999) + -985) % 54) - -344) / 5) + 262);
    	a81 = (((((((a81 * a187) % 14999) - -14017) % 41) + 273) + 591) - 580);
    	a120 = ((((((((a120 * a156) % 14999) - -3022) % 101) + 329) - 147) * 15) / 10);
    	a61 = ((a147 / a83) - -11);
    	a184 = (a45 - 2); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
}
 void calculate_outputm109(int input) {
    if((a117 == 10 && (a117 == 10 && ((a147 == 11 && ((((input == 3) &&  cf==1 ) && a83 == 11) && ((150 < a159) && (216 >= a159)))) && a117 == 10)))) {
    	a33 += (a33 + 20) > a33 ? 1 : 0;
    	cf = 0;
    	a81 = (((((a81 * a9) % 14999) + -12373) + -5273) + -5759);
    	a196 = ((a26 + a184) + 2);
    	a75 = ((a117 * a45) - 72);
    	a58 = (((((a81 * a81) % 14999) - 14988) / 5) + -20031);
    	a187 = (((((((a9 * a9) % 14999) - 19515) * 10) / 9) * 10) / 9);
    	a102 = (((((a102 * a9) % 14999) - 3092) - 19599) + -6865);
    	a159 = (((((a159 * a187) % 14999) / 5) - 18511) + -3936);
    	a27 = (a117 + -2);
    	a184 = (a75 - 4);
    	a16 = ((((((a58 * a9) % 14999) - -13341) / 5) / 5) + -12414);
    	a130 = ((a45 + a45) - 12);
    	a156 = (((((a58 * a9) % 14999) / 5) + -8718) - 1898);
    	a100 = (((((a100 * a120) - -471) - 14396) + 13663) + -20563);
    	a61 = (a195 - 1);
    	a66 = ((a184 * a184) + -10);
    	a120 = ((((((a120 * a16) % 14999) - 14886) + -54) + 4897) - 4875);
    	a26 = (a130 - 1);
    	a117 = ((a45 + a27) - 7);
    	a147 = (a83 + -1);
    	a83 = (a196 + -1);
    	a9 = ((((((a9 * a156) % 14999) / 5) + -4744) * 10) / 9); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if(((((196 < a102) && (314 >= a102)) && (((146 < a120) && (263 >= a120)) && ((146 < a120) && (263 >= a120)))) && (((( cf==1  && (input == 5)) && a61 == 11) && ((125 < a16) && (290 >= a16))) && ((44 < a156) && (168 >= a156))))) {
    	a42 -= (a42 - 20) < a42 ? 4 : 0;
    	cf = 0;
    	a120 = (((((((a120 * a187) % 14999) * 2) - 2) / 5) % 101) - -364);
    	a187 = (((((((a9 * a120) % 14999) % 99) - -57) * 5) % 99) + 82);
    	a7 = ((((((a9 * a156) % 14999) - 20906) * 1) * 10) / 9);
    	a181 = (((((((a7 * a7) % 14999) % 14793) + 15205) / 5) * 5) + 5);
    	a156 = (((((((a58 * a120) % 14999) + 12857) - -780) * 1) % 104) - -239);
    	a147 = (a75 - -2);
    	a102 = (((((((a102 * a120) % 14999) % 83) + 334) * 1) / 5) + 371);
    	a26 = (a195 - 6);
    	a61 = a147;
    	a117 = (a130 - -5);
    	a100 = ((((((a100 * a181) % 14999) % 49) - -93) * 1) + 2);
    	a81 = ((((((a81 * a16) % 14999) - -12899) % 41) - -278) - -16);
    	a16 = (((((((a120 * a58) % 14999) % 54) - -291) * 5) % 54) + 293);
    	a159 = ((((((a159 * a102) % 14999) / 5) - 11301) % 38) + 264);
    	a184 = (a147 - 6);
    	a83 = a61;
    	a9 = ((((((a9 * a120) % 14999) + -20378) * 1) % 34) - -284); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if(((((159 < a9) && (223 >= a9)) && ((input == 2) &&  cf==1 )) && (a83 == 11 && (a147 == 11 && ((((44 < a156) && (168 >= a156)) && ((-176 < a187) && (39 >= a187))) && ((-176 < a187) && (39 >= a187))))))) {
    	a164 -= (a164 - 20) < a164 ? 1 : 0;
    	cf = 0;
    	 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
}
 void calculate_outputm16(int input) {
    if(((((((196 < a102) && (314 >= a102)) && a184 == 5) && ((-176 < a187) && (39 >= a187))) && a147 == 11) && (a61 == 11 && (((159 < a9) && (223 >= a9)) && (a195 == 4 &&  cf==1 ))))) {
    	calculate_outputm105(input);
    } 
    if(((((125 < a16) && (290 >= a16)) && a27 == 9) && (a26 == 4 && (a117 == 10 && (((84 < a81) && (272 >= a81)) && (( cf==1  && a195 == 8) && ((146 < a120) && (263 >= a120)))))))) {
    	calculate_outputm108(input);
    } 
    if((((a61 == 11 && (((a83 == 11 && (a195 == 11 &&  cf==1 )) && ((146 < a120) && (263 >= a120))) && ((150 < a159) && (216 >= a159)))) && ((196 < a102) && (314 >= a102))) && ((146 < a120) && (263 >= a120)))) {
    	calculate_outputm109(input);
    } 
}
 void calculate_outputm111(int input) {
    if(((((216 < a159) && (294 >= a159)) && ((((input == 5) &&  cf==1 ) && ((263 < a120) && (466 >= a120))) && a147 == 12)) && (((223 < a9) && (292 >= a9)) && (a26 == 5 && ((223 < a9) && (292 >= a9)))))) {
    	a151 -= (a151 - 20) < a151 ? 3 : 0;
    	cf = 0;
    	a45 = (a130 + 2);
    	a26 = (a27 - 6);
    	a187 = ((((((((a187 * a102) % 14999) - 26462) % 107) + 37) * 5) % 107) + -67);
    	a9 = (((((((a120 * a102) % 14999) % 31) - -169) * 5) % 31) - -168);
    	a100 = (((((((a100 * a58) % 14999) % 36) - 22) + -8850) / 5) + 1752);
    	a184 = (a147 - 7);
    	a117 = (a83 + -2);
    	a147 = (a26 - -7);
    	a156 = (((((((a156 * a58) % 14999) % 61) - -58) + -14314) * 2) + 28558);
    	a195 = (a45 + 3);
    	a83 = (a75 - -1);
    	a61 = (a26 - -7);
    	a159 = ((((((a159 * a16) % 14999) + -14251) / 5) % 32) + 184);
    	a16 = (((((((a16 * a58) % 14999) / 5) / 5) - 2026) % 82) - -253);
    	a120 = ((((((a120 * a181) % 14999) + -3381) - -724) % 58) + 204);
    	a81 = ((((((((a81 * a9) % 14999) % 93) + 140) * 9) / 10) + -9575) + 9610);
    	a102 = (((((((a102 * a7) % 14999) % 58) + 254) + 2) + -694) + 694); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((a130 == 6 && a27 == 10) && ((39 < a187) && (238 >= a187))) && (a75 == 10 && (a83 == 12 && (((39 < a187) && (238 >= a187)) && ( cf==1  && (input == 3))))))) {
    	a97 -= (a97 - 20) < a97 ? 2 : 0;
    	a5 += (a5 + 20) > a5 ? 2 : 0;
    	a64 -= (a64 - 20) < a64 ? 4 : 0;
    	cf = 0;
    	a27 = (a130 + 2);
    	a156 = (((((a156 * a9) % 14999) + -20136) - 1343) * 1);
    	a26 = ((a27 * a83) - 93);
    	a100 = ((((((a100 * a16) % 14999) / 5) - 5817) - -17118) + -15949);
    	a184 = ((a147 - a130) + -2);
    	a117 = (a27 - -1);
    	a120 = (((((a7 * a7) % 14999) - 14993) - -22017) + -22021);
    	a159 = (((((a159 * a9) % 14999) - 11955) - 4482) + -4044);
    	a172 = (a61 - 7);
    	a66 = (a147 + -9);
    	a81 = (((((a81 * a102) % 14999) + -20769) + -2364) * 1);
    	a83 = ((a26 - a27) + 15);
    	a61 = (a130 + 4);
    	a58 = ((((((a58 * a7) % 14999) / 5) + -15630) * 10) / 9);
    	a16 = ((((((a16 * a102) % 14999) - -7695) / 5) / 5) - 21990);
    	a9 = (((((a120 * a7) % 14999) + 12083) * 1) - 26991);
    	a102 = (((((a181 * a120) % 14999) - 14817) - 184) - 0);
    	a75 = ((a27 / a130) - -7);
    	a187 = ((((((a187 * a120) % 14999) % 14912) + -15087) - 1) - 0);
    	a147 = (a27 - -2);
    	a130 = (a27 + -4); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
}
 void calculate_outputm17(int input) {
    if(((((290 < a16) && (399 >= a16)) && ((412 < a181 &&  cf==1 ) && a184 == 6)) && ((((272 < a81) && (355 >= a81)) && (a61 == 12 && ((168 < a156) && (378 >= a156)))) && a117 == 11))) {
    	calculate_outputm111(input);
    } 
}
 void calculate_outputm123(int input) {
    if((((((272 < a81) && (355 >= a81)) && ((a83 == 12 && a184 == 6) && a147 == 12)) && (a26 == 5 && (((142 < a58) && (282 >= a58)) && ( cf==1  && (input == 4))))) && a108 == 8942)) {
    	a137 += (a137 + 20) > a137 ? 2 : 0;
    	cf = 0;
    	a28 = (((((((a159 * a9) % 14999) + 2674) - 14801) + 70) % 59) - -192);
    	a7 = (((((a7 * a156) % 14999) + 3421) + 8383) * 1); 
    	 printf("%d\n", 22); fflush(stdout); 
    } 
    if((((((263 < a120) && (466 >= a120)) && ((((223 < a9) && (292 >= a9)) && ((((168 < a156) && (378 >= a156)) && ( cf==1  && (input == 2))) && ((142 < a58) && (282 >= a58)))) && ((290 < a16) && (399 >= a16)))) && a75 == 10) && a5 == 1396)) {
    	a76 += (a76 + 20) > a76 ? 4 : 0;
    	cf = 0;
    	a172 = (a26 - -5);
    	a66 = (a27 + -7);
    	a100 = ((((((a100 * a187) % 14999) + -21503) * 1) + 22617) - 30106); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((((142 < a58) && (282 >= a58)) && ( cf==1  && (input == 5))) && ((142 < a58) && (282 >= a58))) && (a83 == 12 && (((272 < a81) && (355 >= a81)) && (((314 < a102) && (482 >= a102)) && ((216 < a159) && (294 >= a159))))))) {
    	a43 -= (a43 - 20) < a43 ? 2 : 0;
    	cf = 0;
    	a172 = ((a0 * a27) - 122);
    	a58 = (((36 * -5) + 5907) * -5);
    	a100 = (((((a100 * a9) % 14999) + -27039) - 2057) - 895);
    	a102 = (((((a58 * a100) % 14999) + -1087) * 1) + -13903);
    	a75 = ((a184 / a184) - -7);
    	a156 = (((((a58 * a58) % 14999) + -14996) + -1) - 4);
    	a117 = ((a26 - a27) - -14);
    	a16 = (((((a58 * a58) % 14999) / 5) + -21663) * 1);
    	a187 = (((((((a187 * a102) % 14999) - 8757) * 1) * 1) % 14912) + -15087);
    	a120 = ((((((a120 * a81) % 14999) + 5975) * 1) + -11825) - 16700);
    	a66 = (a172 - 5);
    	a61 = (a130 - -4);
    	a81 = (((((a81 * a16) % 14999) / 5) + 10842) / -5);
    	a147 = (a130 - -4);
    	a9 = (((((a9 * a7) % 14999) - -13353) - 17112) + -20256);
    	a83 = ((a172 / a61) + 10);
    	a159 = (((((a159 * a156) % 14999) + -14968) * 1) - 31);
    	a26 = (a184 - 3);
    	a184 = (a172 - 4);
    	a27 = (a147 - 2);
    	a130 = (a117 + -5); 
    	 printf("%d\n", 22); fflush(stdout); 
    } 
    if((((((142 < a58) && (282 >= a58)) && (a147 == 12 && (a83 == 12 && (( cf==1  && (input == 3)) && ((290 < a16) && (399 >= a16)))))) && (a27 == 10 && ((168 < a156) && (378 >= a156)))) && (a186 % 2==0))) {
    	a164 -= (a164 - 20) < a164 ? 4 : 0;
    	cf = 0;
    	a100 = (((((a100 * a120) % 14999) + 14129) - -673) / 5);
    	a148 = ((((((a100 * a9) % 14999) + 14167) % 52) + -25) / 5);
    	a90 = (a130 + 4); 
    	 printf("%d\n", 22); fflush(stdout); 
    } 
    if(((((((272 < a81) && (355 >= a81)) && (( cf==1  && (input == 1)) && a147 == 12)) && a26 == 5) && ((a26 == 5 && a83 == 12) && ((142 < a58) && (282 >= a58)))) && (a34 % 2==0))) {
    	a68 += (a68 + 20) > a68 ? 2 : 0;
    	cf = 0;
    	a176 = ((a0 * a27) + -129);
    	a7 = ((((((a7 * a58) % 14999) - 18614) % 41) - -129) - 33); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
}
 void calculate_outputm19(int input) {
    if(((a0 == 13 &&  cf==1 ) && ((((((39 < a187) && (238 >= a187)) && (((223 < a9) && (292 >= a9)) && a61 == 12)) && a26 == 5) && ((216 < a159) && (294 >= a159))) && ((223 < a9) && (292 >= a9))))) {
    	calculate_outputm123(input);
    } 
}
 void calculate_outputm136(int input) {
    if((((a83 == 12 && (((input == 1) &&  cf==1 ) && a184 == 6)) && (((a130 == 6 && a147 == 12) && a147 == 12) && ((168 < a156) && (378 >= a156)))) && a68 <= 3)) {
    	a138 -= (a138 - 20) < a138 ? 3 : 0;
    	cf = 0;
    	a148 = ((((a148 * a187) + 20573) + 1415) / 5);
    	a167 = ((a26 + a61) + -10); 
    	 printf("%d\n", 25); fflush(stdout); 
    } 
    if((((((263 < a120) && (466 >= a120)) && (((290 < a16) && (399 >= a16)) && (((((input == 3) &&  cf==1 ) && ((290 < a16) && (399 >= a16))) && ((168 < a156) && (378 >= a156))) && ((216 < a159) && (294 >= a159))))) && a117 == 11) && a164 >= 8)) {
    	cf = 0;
    	a58 = (((((a81 * a81) % 14999) + 1874) / 5) + -17746);
    	a66 = (a26 - -2);
    	a61 = (a147 - 2);
    	a100 = (((((((a100 * a81) % 14999) - 7824) * 3) - -7951) % 14985) + -15014);
    	a159 = (((((a58 * a9) % 14999) + -9022) + -5853) - 48);
    	a78 = ((((((a156 * a187) % 14999) + 14549) - -79) - 29715) + 19465);
    	a27 = (a75 - 2);
    	a184 = (a147 - 8);
    	a102 = ((((((a102 * a120) % 14999) - 17514) + 11476) - 6623) - 4576);
    	a187 = ((((((a16 * a159) % 14999) % 14912) - 15087) / 5) + -19263);
    	a117 = (a147 + -3);
    	a156 = ((((((a100 * a159) % 14999) - 6355) * 1) / 5) - 4435);
    	a81 = ((((((a81 * a159) % 14999) * 2) / 5) + -5505) + -12065); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if(((((a83 == 12 && ((314 < a102) && (482 >= a102))) && a61 == 12) && (((((39 < a187) && (238 >= a187)) && ( cf==1  && (input == 4))) && a117 == 11) && a75 == 10)) && a71 == 6378)) {
    	a197 += (a197 + 20) > a197 ? 2 : 0;
    	cf = 0;
    	a66 = ((a130 / a27) - -8);
    	a195 = ((a90 - a83) + 2);
    	a100 = (((((a100 * a187) % 14999) - 18437) / 5) - 9212); 
    	 printf("%d\n", 22); fflush(stdout); 
    } 
    if((((a184 == 6 && (a26 == 5 && ((39 < a187) && (238 >= a187)))) && (a184 == 6 && ((a83 == 12 && ( cf==1  && (input == 2))) && a130 == 6))) && a101 == 4166)) {
    	cf = 0;
    	a45 = ((a61 + a90) - 26);
    	a39 = (a75 - 2);
    	a100 = ((((((a100 * a120) % 14999) % 36) - -6) + 1) / 5); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if((((a26 == 5 && ( cf==1  && (input == 5))) && ((216 < a159) && (294 >= a159))) && (((((142 < a58) && (282 >= a58)) && ((216 < a159) && (294 >= a159))) && ((39 < a187) && (238 >= a187))) && ((263 < a120) && (466 >= a120))))) {
    	a60 += (a60 + 20) > a60 ? 2 : 0;
    	cf = 0;
    	a130 = (a117 - 6);
    	a9 = ((((((((a156 * a156) % 14999) % 31) + 172) * 5) - -16960) % 31) + 188);
    	a81 = ((((((a81 * a9) % 14999) - 13282) % 93) - -178) + 1);
    	a26 = ((a184 - a90) - -13);
    	a100 = ((((((a100 * a58) % 14999) % 36) - 20) + -7916) - -7914);
    	a102 = ((((((a102 * a187) % 14999) - -9367) / 5) % 58) + 205);
    	a83 = (a61 + -1);
    	a58 = (((((a148 * a148) % 65) - -76) + 1) + 1);
    	a75 = ((a83 * a184) - 57);
    	a45 = ((a184 - a184) + 6);
    	a187 = (((((((a187 * a16) % 14999) / 5) % 107) + -97) + -3694) - -3701);
    	a27 = (a147 + -3);
    	a61 = (a130 - -6);
    	a16 = (((((((a156 * a156) % 14999) - -7112) + 921) / 5) % 82) - -205);
    	a159 = ((((((((a159 * a156) % 14999) - 6175) % 32) + 184) * 5) % 32) + 178);
    	a120 = ((((((((a120 * a102) % 14999) % 58) - -160) * 10) / 9) - 28287) + 28263);
    	a157 = (a147 - -1);
    	a147 = (a130 + 6);
    	a184 = ((a130 + a130) - 5);
    	a156 = ((((((a156 * a148) % 61) + 106) + 18083) * 1) + -18083); 
    	 printf("%d\n", 19); fflush(stdout); 
    } 
}
 void calculate_outputm22(int input) {
    if((( cf==1  && a90 == 15) && ((((((39 < a187) && (238 >= a187)) && (a83 == 12 && a75 == 10)) && ((314 < a102) && (482 >= a102))) && a26 == 5) && ((272 < a81) && (355 >= a81))))) {
    	calculate_outputm136(input);
    } 
}
 void calculate_outputm140(int input) {
    if(((((272 < a81) && (355 >= a81)) && ((a75 == 10 && a117 == 11) && a27 == 10)) && ((((142 < a58) && (282 >= a58)) && ((input == 5) &&  cf==1 )) && a75 == 10))) {
    	a191 += (a191 + 20) > a191 ? 1 : 0;
    	a33 += (a33 + 20) > a33 ? 1 : 0;
    	cf = 0;
    	a58 = ((((((a180 * a81) % 14999) + 3306) % 65) + 62) + 10);
    	a195 = (a147 + -8);
    	a45 = (a75 + -2);
    	a100 = ((((((a100 * a102) % 14999) + -29205) % 36) + 13) + -2);
    	a27 = (a195 + 5);
    	a75 = (a117 - 2);
    	a120 = (((((((a120 * a180) % 14999) % 58) - -186) + -38) + -29293) - -29320);
    	a184 = (a83 + -7);
    	a147 = (a45 - -3);
    	a187 = ((((((a81 * a159) % 14999) + 3658) % 107) + -117) / 5);
    	a26 = ((a184 + a75) - 10);
    	a83 = ((a130 / a130) - -10);
    	a16 = ((((((a16 * a58) % 14999) % 82) - -167) - -23402) - 23413);
    	a117 = 10;
    	a61 = (a45 - -3);
    	a156 = (((((a156 * a100) - -6064) % 61) + 105) + 0);
    	a102 = ((((((a102 * a148) % 14999) / 5) - -4997) % 58) + 216);
    	a81 = ((((((a81 * a187) % 14999) % 93) + 178) * 1) * 1); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((((input == 2) &&  cf==1 ) && a184 == 6) && ((39 < a187) && (238 >= a187))) && (((((168 < a156) && (378 >= a156)) && ((314 < a102) && (482 >= a102))) && a83 == 12) && a26 == 5))) {
    	a67 += (a67 + 20) > a67 ? 1 : 0;
    	cf = 0;
    	a26 = (a184 - 3);
    	a117 = (a147 + -3);
    	a130 = (a26 + 1);
    	a9 = (((((a81 * a81) % 14999) - -1108) + -28416) - 2198);
    	a66 = (a75 + -6);
    	a159 = ((((((a81 * a81) % 14999) / 5) + -9784) - -11784) + -25133);
    	a184 = ((a117 - a130) + -1);
    	a121 = (a75 + -7);
    	a100 = (((((a100 * a102) % 14999) - 24560) + -3196) + -1814);
    	a187 = ((((((a180 * a9) % 14999) % 14912) + -15087) * 1) + -1);
    	a61 = ((a26 / a83) + 10);
    	a102 = ((((((a58 * a9) % 14999) * 2) % 15098) + -14901) + 0);
    	a120 = (((((a120 * a9) % 14999) + 13696) * 1) + -28566);
    	a83 = (a26 + 7);
    	a16 = ((((((a16 * a148) % 14999) - 22139) + -4935) - -20648) - 14155);
    	a27 = ((a147 * a75) + -112);
    	a156 = (((((a156 * a187) % 14999) + -9912) * 1) + -3497);
    	a75 = ((a147 * a147) - 136);
    	a58 = ((((((a159 * a81) % 14999) + -14993) + 17430) / 5) - 9072);
    	a81 = ((((((a81 * a9) % 14999) - -12048) / 5) - -23685) * -1);
    	a147 = (a27 - -2); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
}
 void calculate_outputm23(int input) {
    if(((((((168 < a156) && (378 >= a156)) && ((263 < a120) && (466 >= a120))) && a26 == 5) && a184 == 6) && (a61 == 12 && ((98 < a180 &&  cf==1 ) && ((290 < a16) && (399 >= a16)))))) {
    	calculate_outputm140(input);
    } 
}
 void calculate_outputm143(int input) {
    if(((a27 == 10 && ((((290 < a16) && (399 >= a16)) && (a184 == 6 && ((( cf==1  && (input == 1)) && ((39 < a187) && (238 >= a187))) && a26 == 5))) && a184 == 6)) && a15 == 2690)) {
    	a68 += (a68 + 20) > a68 ? 3 : 0;
    	cf = 0;
    	a100 = (((((((a100 * a81) % 14999) % 49) + 58) / 5) + -7722) + 7804);
    	a7 = ((((((a159 * a159) % 14999) + 4602) % 54) - -179) - -8);
    	a0 = ((a26 * a75) + -38); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
    if((((((223 < a9) && (292 >= a9)) && (a26 == 5 && (a75 == 10 && a26 == 5))) && ((((39 < a187) && (238 >= a187)) && ( cf==1  && (input == 4))) && ((142 < a58) && (282 >= a58)))) && a76 <= 3)) {
    	a138 -= (a138 - 20) < a138 ? 4 : 0;
    	cf = 0;
    	a184 = ((a147 - a26) - 3);
    	a156 = ((((((a156 * a187) % 14999) + -25384) * 10) / 9) / 5);
    	a26 = (a117 - 8);
    	a27 = (a61 + -4);
    	a81 = (((((a81 * a148) % 14999) / 5) + -17756) * 1);
    	a66 = (a130 + -4);
    	a100 = (((((a100 * a102) % 14999) + -18872) + -7011) * 1);
    	a166 = a167;
    	a61 = a75;
    	a117 = (a27 - -1);
    	a130 = ((a27 - a83) + 8);
    	a102 = (((((a16 * a58) % 14999) - 28440) + -1023) * 1);
    	a159 = (((((a159 * a9) % 14999) + -23833) * 1) - -763);
    	a75 = (a130 - -4); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((a147 == 12 && ((290 < a16) && (399 >= a16))) && a83 == 12) && (a147 == 12 && ((((290 < a16) && (399 >= a16)) && ( cf==1  && (input == 3))) && a75 == 10)))) {
    	a138 -= (a138 - 20) < a138 ? 1 : 0;
    	cf = 0;
    	a39 = ((a27 / a167) + 10);
    	a27 = (a184 + 3);
    	a9 = ((((((a148 * a148) % 14999) % 31) + 173) + 18182) - 18170);
    	a130 = (a39 + -6);
    	a16 = (((((((a148 * a148) % 14999) - -1519) + -30065) - -5440) % 82) + 258);
    	a45 = (a61 + -11);
    	a75 = ((a39 / a184) - -8);
    	a26 = (a39 + -7);
    	a156 = ((((((a156 * a58) % 14999) + 4926) - -1251) % 61) + 49);
    	a120 = ((((((a120 * a16) % 14999) % 58) - -148) - 1) * 1);
    	a100 = ((((((a100 * a58) % 14999) - 15625) % 36) - -43) + 1);
    	a61 = (a184 - -5);
    	a187 = (((((((a187 * a159) % 14999) / 5) + -17107) / 5) % 107) - 14);
    	a117 = ((a130 - a184) - -11);
    	a83 = (a26 + 7);
    	a147 = a39;
    	a58 = (((((((a81 * a9) % 14999) % 65) + 38) * 9) / 10) + 36);
    	a81 = (((((((a81 * a102) % 14999) % 93) + 94) * 5) % 93) - -106);
    	a159 = ((((14 * -5) - -19682) * 1) * -1);
    	a102 = ((((((((a120 * a120) % 14999) % 58) - -249) * 5) - -15644) % 58) + 202);
    	a184 = (a26 + 1); 
    	 printf("%d\n", 23); fflush(stdout); 
    } 
    if(((a26 == 5 && (a184 == 6 && (((272 < a81) && (355 >= a81)) && ((((263 < a120) && (466 >= a120)) && (a61 == 12 && ( cf==1  && (input == 5)))) && a26 == 5)))) && a112 <= -5)) {
    	a43 -= (a43 - 20) < a43 ? 2 : 0;
    	cf = 0;
    	a100 = (((((a100 * a159) % 14999) / 5) - 20433) - 5054);
    	a66 = ((a61 * a61) + -139);
    	a61 = (a130 + 4);
    	a9 = ((((((a100 * a16) % 14999) / 5) - 4199) * 10) / 9);
    	a184 = (a61 - 6);
    	a102 = (((((a16 * a81) % 14999) + -26837) - 2575) + -278);
    	a119 = ((a75 / a27) - -5);
    	a120 = ((((((a120 * a102) % 14999) + -14906) + -20) + 24700) + -24683);
    	a58 = (((((a58 * a187) % 14999) - 25325) + -2494) / 5);
    	a156 = (((((a156 * a9) % 14999) + -14972) - 16) - 12);
    	a26 = (a119 - 3);
    	a117 = ((a83 + a61) + -13);
    	a27 = (a184 + 4);
    	a147 = ((a130 - a75) + 14);
    	a81 = ((((((a81 * a9) % 14999) * 2) % 15042) - 14957) - 0); 
    	 printf("%d\n", 26); fflush(stdout); 
    } 
    if((((a117 == 11 && (((input == 2) &&  cf==1 ) && a26 == 5)) && (a184 == 6 && (a130 == 6 && (((216 < a159) && (294 >= a159)) && ((314 < a102) && (482 >= a102)))))) && a191 >= 1)) {
    	a67 += (a67 + 20) > a67 ? 1 : 0;
    	cf = 0;
    	a27 = (a117 - 2);
    	a45 = ((a75 * a26) - 47);
    	a100 = ((((((((a100 * a148) % 14999) % 36) - 20) - -5390) * 5) % 36) + 5);
    	a147 = (a167 - -2);
    	a102 = ((((((a9 * a120) % 14999) + 10604) + -35319) % 58) + 304);
    	a181 = ((((a100 * a16) - -12026) * 1) - -2);
    	a58 = ((((((a58 * a100) * 2) / 5) * 5) % 65) + 77);
    	a9 = (((((((a9 * a159) % 14999) - -6557) + 904) + 5996) % 31) - -176);
    	a120 = (((((((a120 * a102) % 14999) % 58) - -174) * 10) / 9) + -18);
    	a184 = ((a83 * a83) + -139);
    	a81 = (((((((a81 * a187) % 14999) - -292) % 93) - -158) - -16495) + -16487);
    	a26 = (a45 - -1); 
    	 printf("%d\n", 24); fflush(stdout); 
    } 
}
 void calculate_outputm24(int input) {
    if((((((39 < a187) && (238 >= a187)) && (( cf==1  && a167 == 9) && a83 == 12)) && ((272 < a81) && (355 >= a81))) && (a75 == 10 && (((168 < a156) && (378 >= a156)) && ((168 < a156) && (378 >= a156)))))) {
    	calculate_outputm143(input);
    } 
}

 void calculate_output(int input) {
        cf = 1;

    if((((a184 == 4 && a81 <=  84) && a117 == 9) && (((a27 == 8 && ( cf==1  && a100 <=  -30)) && a61 == 10) && a27 == 8))) {
    	if((((a156 <=  44 && (a27 == 8 && ( cf==1  && a66 == 2))) && a75 == 8) && (a27 == 8 && (a159 <=  150 && a117 == 9)))) {
    		calculate_outputm1(input);
    	} 
    	if(((a184 == 4 && (a58 <=  11 && a16 <=  125)) && (a159 <=  150 && ((a102 <=  196 && (a66 == 3 &&  cf==1 )) && a117 == 9)))) {
    		calculate_outputm2(input);
    	} 
    	if(((a156 <=  44 && (a75 == 8 && ((a9 <=  159 && (a66 == 4 &&  cf==1 )) && a9 <=  159))) && (a187 <=  -176 && a187 <=  -176))) {
    		calculate_outputm3(input);
    	} 
    	if(((a61 == 10 && ( cf==1  && a66 == 6)) && (((a130 == 4 && (a184 == 4 && a147 == 10)) && a156 <=  44) && a81 <=  84))) {
    		calculate_outputm5(input);
    	} 
    	if(((a27 == 8 && a156 <=  44) && (a159 <=  150 && ((a102 <=  196 && (a156 <=  44 && (a66 == 7 &&  cf==1 ))) && a187 <=  -176)))) {
    		calculate_outputm6(input);
    	} 
    } 
    if(((((((159 < a9) && (223 >= a9)) && ((146 < a120) && (263 >= a120))) && ((146 < a120) && (263 >= a120))) && a184 == 5) && (((196 < a102) && (314 >= a102)) && (a147 == 11 && ( cf==1  && ((-30 < a100) && (44 >= a100))))))) {
    	if(((a117 == 10 && ((146 < a120) && (263 >= a120))) && (((84 < a81) && (272 >= a81)) && (((a117 == 10 && ( cf==1  && a45 == 1)) && ((146 < a120) && (263 >= a120))) && ((84 < a81) && (272 >= a81)))))) {
    		calculate_outputm9(input);
    	} 
    	if((((a45 == 2 &&  cf==1 ) && ((11 < a58) && (142 >= a58))) && (((125 < a16) && (290 >= a16)) && ((((159 < a9) && (223 >= a9)) && (a117 == 10 && a117 == 10)) && ((44 < a156) && (168 >= a156)))))) {
    		calculate_outputm10(input);
    	} 
    	if(((a147 == 11 && (a27 == 9 && (a61 == 11 && ((159 < a9) && (223 >= a9))))) && ((((146 < a120) && (263 >= a120)) && (a45 == 4 &&  cf==1 )) && ((196 < a102) && (314 >= a102))))) {
    		calculate_outputm12(input);
    	} 
    	if(((a61 == 11 && (a45 == 6 &&  cf==1 )) && (a27 == 9 && (((a83 == 11 && ((11 < a58) && (142 >= a58))) && ((11 < a58) && (142 >= a58))) && a26 == 4)))) {
    		calculate_outputm14(input);
    	} 
    	if((((a130 == 5 && (a45 == 7 &&  cf==1 )) && ((-176 < a187) && (39 >= a187))) && (a184 == 5 && (((150 < a159) && (216 >= a159)) && (a184 == 5 && ((196 < a102) && (314 >= a102))))))) {
    		calculate_outputm15(input);
    	} 
    	if((((((84 < a81) && (272 >= a81)) && ((( cf==1  && a45 == 8) && ((196 < a102) && (314 >= a102))) && a61 == 11)) && ((150 < a159) && (216 >= a159))) && (((84 < a81) && (272 >= a81)) && a147 == 11))) {
    		calculate_outputm16(input);
    	} 
    } 
    if((((((44 < a100) && (143 >= a100)) &&  cf==1 ) && ((314 < a102) && (482 >= a102))) && (a26 == 5 && (a61 == 12 && ((a117 == 11 && a130 == 6) && ((216 < a159) && (294 >= a159))))))) {
    	if((((a7 <=  54 &&  cf==1 ) && a83 == 12) && ((a26 == 5 && (a83 == 12 && (((168 < a156) && (378 >= a156)) && a27 == 10))) && ((216 < a159) && (294 >= a159))))) {
    		calculate_outputm17(input);
    	} 
    	if((((((263 < a120) && (466 >= a120)) && a61 == 12) && ((272 < a81) && (355 >= a81))) && (a83 == 12 && (a117 == 11 && (a83 == 12 && ( cf==1  && ((137 < a7) && (246 >= a7)))))))) {
    		calculate_outputm19(input);
    	} 
    } 
    if(((( cf==1  && 143 < a100) && ((272 < a81) && (355 >= a81))) && (((263 < a120) && (466 >= a120)) && (((314 < a102) && (482 >= a102)) && (a184 == 6 && (((168 < a156) && (378 >= a156)) && ((272 < a81) && (355 >= a81)))))))) {
    	if(((a130 == 6 && (( cf==1  && ((-73 < a148) && (32 >= a148))) && ((168 < a156) && (378 >= a156)))) && (((263 < a120) && (466 >= a120)) && (((216 < a159) && (294 >= a159)) && (((223 < a9) && (292 >= a9)) && a27 == 10))))) {
    		calculate_outputm22(input);
    	} 
    	if(((((a147 == 12 && a184 == 6) && a26 == 5) && ((168 < a156) && (378 >= a156))) && (((168 < a156) && (378 >= a156)) && (( cf==1  && ((32 < a148) && (162 >= a148))) && a27 == 10)))) {
    		calculate_outputm23(input);
    	} 
    	if(((a75 == 10 && (( cf==1  && 162 < a148) && a61 == 12)) && (((a27 == 10 && a184 == 6) && ((142 < a58) && (282 >= a58))) && a26 == 5))) {
    		calculate_outputm24(input);
    	} 
    } 
    errorCheck();

    if( cf==1 ) {
    	fprintf(stdout, "Invalid input: %d\n", input);
    	ERR = ERR_INVALID_INPUT;
    }
}
