#include <stdio.h>
#include <math.h>
#include <stdlib.h>


// ------------------ W A R N I N G ------------------
// This program simulates a run of Problem12 that may lead to an (expected) overflow.
// RERS 2016 assumes that 32-bit integers are used.
// Please make sure that you are using 32-bit integers when running this program.
//
///////////////////////////////////////////////////////////////////////////////

#define ERR_INVALID_INPUT 999
// Flag that contains the number of the label reached, or negative if none
int ERR;

void __VERIFIER_error(int i) {
	if (ERR >= 0) {
		fprintf(stderr, "Error not reset. Overwriting error code %d.\n", ERR);
	}
	ERR = i;
}

// Reinitialize automaton, see implementation below
void reset_eca();

// Reset flag
void reset_error() {
	ERR = -1;
}

void calculate_output(int);

void run() {
	int prePrefix[] = {1, 2, 8, 2, 7, 7, 3, 8, 1, 1, 3, 10, 1, 3, 10, 8, 1, 8, 4, 10, 1, 3, 6, 8, 7, 8, 7, 2, 3, 1, 4};
	int prePrefixLength = 31;
	for (int i = 0; i < prePrefixLength; ++i) {
		calculate_output(prePrefix[i]);
	}
	unsigned long long n = 0;
	while (ERR < 0) {
		++n;
		calculate_output(3);
	}
	printf("error %d after 'prefix' + %llu * '3'\n", ERR, n);
}

void test_int_size() {
	int n = 0;
	if (sizeof(n) != 4) {
		fprintf(stderr, "You are not using 32-bit integers.");
		exit(1);
	}
}

int main(int argc, char *argv[]) {
	test_int_size();
	reset_eca();
	reset_error();
	run();
	return 0;
}

/////////////////////////////////////////////////////////////////////////////

	// inputs
int inputs[] = { 5, 6, 1, 7, 2, 8, 3, 9, 10, 4 };

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
void calculate_outputm157(int);
void calculate_outputm158(int);
void calculate_outputm159(int);
void calculate_outputm160(int);
void calculate_outputm161(int);
void calculate_outputm162(int);
void calculate_outputm163(int);
void calculate_outputm164(int);
void calculate_outputm165(int);
void calculate_outputm166(int);
void calculate_outputm167(int);
void calculate_outputm168(int);
void calculate_outputm169(int);
void calculate_outputm170(int);
void calculate_outputm171(int);
void calculate_outputm172(int);
void calculate_outputm173(int);
void calculate_outputm174(int);
void calculate_outputm175(int);
void calculate_outputm176(int);
void calculate_outputm177(int);
void calculate_outputm178(int);
void calculate_outputm179(int);
void calculate_outputm180(int);
void calculate_outputm181(int);
void calculate_outputm182(int);
void calculate_outputm183(int);
void calculate_outputm184(int);
void calculate_outputm185(int);
void calculate_outputm186(int);
void calculate_outputm187(int);
void calculate_outputm188(int);
void calculate_outputm189(int);
void calculate_outputm190(int);
void calculate_outputm191(int);
void calculate_outputm192(int);
void calculate_outputm193(int);
void calculate_outputm194(int);
void calculate_outputm195(int);
void calculate_outputm196(int);
void calculate_outputm197(int);
void calculate_outputm198(int);
void calculate_outputm199(int);
void calculate_outputm200(int);
void calculate_outputm201(int);

int a359 = 4;
int a66 = 1;
int a312 = 32;
int a65[] = { 54, 55, 56, 57, 58, 59 };
int a83[] = { 60, 61, 62, 63, 64, 65 };
int a100[] = { 66, 67, 68, 69, 70, 71 };

int *a40 = a65;
int a59 = 33;
int a127[] = { 7, 8, 9, 10, 11, 12, 13, 14 };

int a323 = 10;
int a183 = 34;
int a8 = 12;
int a386 = 160;
int a363[] = { 5, 6, 7, 8, 9, 10, 11, 12 };

int a329 = 32;
int a155 = 32;
int a263[] = { 1, 2, 3, 4, 5, 6 };
int a241[] = { 7, 8, 9, 10, 11, 12 };
int a399[] = { 13, 14, 15, 16, 17, 18 };

int *a353 = a241;
int a189[] = { 19, 20, 21, 22, 23, 24 };
int a116[] = { 25, 26, 27, 28, 29, 30 };
int a117[] = { 31, 32, 33, 34, 35, 36 };

int *a137 = a189;
int a262[] = { 91, 92, 93, 94, 95, 96 };
int a223[] = { 97, 98, 99, 100, 101, 102 };
int a259[] = { 103, 104, 105, 106, 107, 108 };

int *a275 = a262;
int a92[] = { 8, 9, 10, 11, 12, 13, 14, 15 };

int a71 = 1;
int a368 = 0;
int a206 = 5;
int a201 = -151;
int cf = 1;
int a348[] = { 65, 66, 67, 68, 69, 70 };
int a351[] = { 71, 72, 73, 74, 75, 76 };
int a335[] = { 77, 78, 79, 80, 81, 82 };

int *a358 = a351;
int a73 = 153;
int a54 = 149;
int a235 = 8;
int a243 = -173;
int a16 = 0;
int a339 = 0;
int a269 = 32;
int a372[] = { 7, 8, 9, 10, 11, 12, 13, 14 };
int a157[] = { 8, 9, 10, 11, 12, 13, 14, 15 };

int a224 = 32;
int a172 = 6;
int a295 = 9;
int a81 = 4;
int a139 = 36;
int a336 = 0;
int a151 = 0;
int a196 = 16;
int a132 = 0;
int a129 = 14;
int a102 = 14;
int a79[] = { 6, 7, 8, 9, 10, 11, 12, 13 };

int a320 = 7;
int a221 = 0;
int a303[] = { 42, 43, 44, 45, 46, 47 };
int a293[] = { 48, 49, 50, 51, 52, 53 };
int a376[] = { 54, 55, 56, 57, 58, 59 };

int *a265 = a293;
int a212[] = { 78, 79, 80, 81, 82, 83 };
int a384[] = { 84, 85, 86, 87, 88, 89 };
int a362[] = { 90, 91, 92, 93, 94, 95 };

int *a296 = a384;
int a324 = 9;
int a260 = 0;
int a232[] = { 8, 9, 10, 11, 12, 13, 14, 15 };

int a123 = 1;
int a217[] = { 9, 10, 11, 12, 13, 14, 15, 16 };
int a216[] = { 7, 8, 9, 10, 11, 12, 13, 14 };

int a142 = 0;
int a398 = 11;
int a125 = 12;
int a141 = 12;
int a326[] = { 2, 3, 4, 5, 6, 7, 8, 9 };
int a242[] = { 31, 32, 33, 34, 35, 36 };
int a299[] = { 37, 38, 39, 40, 41, 42 };
int a268[] = { 43, 44, 45, 46, 47, 48 };

int *a239 = a299;
int a87[] = { 4, 5, 6, 7, 8, 9, 10, 11 };
int a115[] = { 4, 5, 6, 7, 8, 9, 10, 11 };

int a130 = 127;
int a170 = 72;
int a378 = 0;
int a148[] = { 21, 22, 23, 24, 25, 26 };
int a119[] = { 27, 28, 29, 30, 31, 32 };
int a18[] = { 33, 34, 35, 36, 37, 38 };

int *a46 = a18;
int a253[] = { 96, 97, 98, 99, 100, 101 };
int a289[] = { 102, 103, 104, 105, 106, 107 };
int a250[] = { 108, 109, 110, 111, 112, 113 };

int *a276 = a289;
int a1 = 6;
int a97 = 0;
int a234 = 8;
int a310 = 187;
int a36 = 306;
int a245[] = { 9, 10, 11, 12, 13, 14 };
int a354[] = { 15, 16, 17, 18, 19, 20 };
int a290[] = { 21, 22, 23, 24, 25, 26 };

int *a274 = a245;
int a30[] = { 5, 6, 7, 8, 9, 10, 11, 12 };

int a397 = 11;
int a191 = 14;
int a146 = 1;
int a300 = 0;
int a307 = 3;
int a286 = 3;
int a383 = 5;
int a111[] = { 44, 45, 46, 47, 48, 49 };
int a60[] = { 50, 51, 52, 53, 54, 55 };
int a188[] = { 56, 57, 58, 59, 60, 61 };

int *a197 = a60;
int a205[] = { 5, 6, 7, 8, 9, 10, 11, 12 };

int a270 = 11;
int a237 = 4;
int a302 = 11;
int a69 = 32;
int a211 = 2;
int a53 = 116;
int a278 = 8;
int a91 = 9;
int a128 = 10;
int a240 = 0;
int a173 = 32;
int a13 = 338;
int a42 = 2;
int a136 = 7;
int a26[] = { 4, 5, 6, 7, 8, 9, 10, 11 };

int a134 = 1;
int a373 = 0;
int a72 = 93;
int a382 = -46;
int a152[] = { 6, 7, 8, 9, 10, 11 };
int a144[] = { 12, 13, 14, 15, 16, 17 };
int a153[] = { 18, 19, 20, 21, 22, 23 };

int *a39 = a153;
int a249 = 346;
int a179 = -10;
int a154 = 13;
int a135 = 35;
int a225 = 6;
int a200 = 9;
int a167[] = { 2, 3, 4, 5, 6, 7, 8, 9 };

int a207 = 32;
int a37[] = { 7, 8, 9, 10, 11, 12, 13, 14 };

int a77 = 12;
int a99 = 5;
int a333 = -26;
int a171 = 33;
int a75 = 32;
int a14 = 8;
int a230 = 4;
int a244 = 11;
int a208[] = { 34, 35, 36, 37, 38, 39 };
int a257[] = { 40, 41, 42, 43, 44, 45 };
int a304[] = { 46, 47, 48, 49, 50, 51 };

int *a392 = a257;
int a357 = -187;
int a109[] = { 45, 46, 47, 48, 49, 50 };
int a193[] = { 51, 52, 53, 54, 55, 56 };
int a114[] = { 57, 58, 59, 60, 61, 62 };

int *a3 = a109;
int a277 = 85;
int a57 = 14;
int a338 = 4;
int a105 = 36;
int a361 = 32;
int a395 = 0;
int a19 = 254;
int a143 = 35;
int a17 = 257;
int a294[] = { 2, 3, 4, 5, 6, 7, 8, 9 };

int a7 = 1;
int a313 = 32;
int a64 = 0;
int a318[] = { 22, 23, 24, 25, 26, 27 };
int a285[] = { 28, 29, 30, 31, 32, 33 };
int a311[] = { 34, 35, 36, 37, 38, 39 };

int *a370 = a285;
int a158 = 5;
int a218 = 32;
int a366[] = { 7, 8, 9, 10, 11, 12, 13, 14 };

int a107 = 33;
int a44 = 33;
int a256 = 32;
int a346[] = { 10, 11, 12, 13, 14, 15, 16, 17 };
int a227[] = { 2, 3, 4, 5, 6, 7, 8, 9 };

int a202 = 10;
int a47[] = { 8, 9, 10, 11, 12, 13, 14, 15 };

int a210 = 0;
int a184 = 14;
int a20[] = { 76, 77, 78, 79, 80, 81 };
int a58[] = { 82, 83, 84, 85, 86, 87 };
int a85[] = { 88, 89, 90, 91, 92, 93 };

int *a195 = a58;
int a226[] = { 4, 5, 6, 7, 8, 9, 10, 11 };
int a68[] = { 5, 6, 7, 8, 9, 10 };
int a199[] = { 11, 12, 13, 14, 15, 16 };
int a76[] = { 17, 18, 19, 20, 21, 22 };

int *a25 = a68;
int a229[] = { 44, 45, 46, 47, 48, 49 };
int a264[] = { 50, 51, 52, 53, 54, 55 };
int a292[] = { 56, 57, 58, 59, 60, 61 };

int *a228 = a264;
int a175[] = { 1, 2, 3, 4, 5, 6, 7, 8 };

int a177 = 32;
int a120 = 1;
int a131 = -15;
int a164 = 1;
int a122 = 3;
int a165 = 1;
int a89 = 1;
int a174 = 1;
int a63 = 3;
int a12 = 1;
int a67 = 0;
int a169 = 2;
int a133 = 1;
int a35 = 1;
int a50 = 1;
int a98 = 1;
int a162 = 2;
int a56 = -15;
int a178 = 1;
int a5 = 3;
int a90 = 1;
int a110 = -15;
int a51 = 1;
int a156 = -15;
int a93 = -15;
int a181 = 1;
int a94 = 1;
int a31 = 1;
int a88 = -15;
int a161 = 3;
int a168 = 1;

void reset_eca() {
	a359 = 4;
	a66 = 1;
	a312 = 32;
	a65[0] = 54;
	a65[1] = 55;
	a65[2] = 56;
	a65[3] = 57;
	a65[4] = 58;
	a65[5] = 59;
	a83[0] = 60;
	a83[1] = 61;
	a83[2] = 62;
	a83[3] = 63;
	a83[4] = 64;
	a83[5] = 65;
	a100[0] = 66;
	a100[1] = 67;
	a100[2] = 68;
	a100[3] = 69;
	a100[4] = 70;
	a100[5] = 71;
	a40 = a65;
	a59 = 33;
	a127[0] = 7;
	a127[1] = 8;
	a127[2] = 9;
	a127[3] = 10;
	a127[4] = 11;
	a127[5] = 12;
	a127[6] = 13;
	a127[7] = 14;
	a323 = 10;
	a183 = 34;
	a8 = 12;
	a386 = 160;
	a363[0] = 5;
	a363[1] = 6;
	a363[2] = 7;
	a363[3] = 8;
	a363[4] = 9;
	a363[5] = 10;
	a363[6] = 11;
	a363[7] = 12;
	a329 = 32;
	a155 = 32;
	a263[0] = 1;
	a263[1] = 2;
	a263[2] = 3;
	a263[3] = 4;
	a263[4] = 5;
	a263[5] = 6;
	a241[0] = 7;
	a241[1] = 8;
	a241[2] = 9;
	a241[3] = 10;
	a241[4] = 11;
	a241[5] = 12;
	a399[0] = 13;
	a399[1] = 14;
	a399[2] = 15;
	a399[3] = 16;
	a399[4] = 17;
	a399[5] = 18;
	a353 = a241;
	a189[0] = 19;
	a189[1] = 20;
	a189[2] = 21;
	a189[3] = 22;
	a189[4] = 23;
	a189[5] = 24;
	a116[0] = 25;
	a116[1] = 26;
	a116[2] = 27;
	a116[3] = 28;
	a116[4] = 29;
	a116[5] = 30;
	a117[0] = 31;
	a117[1] = 32;
	a117[2] = 33;
	a117[3] = 34;
	a117[4] = 35;
	a117[5] = 36;
	a137 = a189;
	a262[0] = 91;
	a262[1] = 92;
	a262[2] = 93;
	a262[3] = 94;
	a262[4] = 95;
	a262[5] = 96;
	a223[0] = 97;
	a223[1] = 98;
	a223[2] = 99;
	a223[3] = 100;
	a223[4] = 101;
	a223[5] = 102;
	a259[0] = 103;
	a259[1] = 104;
	a259[2] = 105;
	a259[3] = 106;
	a259[4] = 107;
	a259[5] = 108;
	a275 = a262;
	a92[0] = 8;
	a92[1] = 9;
	a92[2] = 10;
	a92[3] = 11;
	a92[4] = 12;
	a92[5] = 13;
	a92[6] = 14;
	a92[7] = 15;
	a71 = 1;
	a368 = 0;
	a206 = 5;
	a201 = -151;
	cf = 1;
	a348[0] = 65;
	a348[1] = 66;
	a348[2] = 67;
	a348[3] = 68;
	a348[4] = 69;
	a348[5] = 70;
	a351[0] = 71;
	a351[1] = 72;
	a351[2] = 73;
	a351[3] = 74;
	a351[4] = 75;
	a351[5] = 76;
	a335[0] = 77;
	a335[1] = 78;
	a335[2] = 79;
	a335[3] = 80;
	a335[4] = 81;
	a335[5] = 82;
	a358 = a351;
	a73 = 153;
	a54 = 149;
	a235 = 8;
	a243 = -173;
	a16 = 0;
	a339 = 0;
	a269 = 32;
	a372[0] = 7;
	a372[1] = 8;
	a372[2] = 9;
	a372[3] = 10;
	a372[4] = 11;
	a372[5] = 12;
	a372[6] = 13;
	a372[7] = 14;
	a157[0] = 8;
	a157[1] = 9;
	a157[2] = 10;
	a157[3] = 11;
	a157[4] = 12;
	a157[5] = 13;
	a157[6] = 14;
	a157[7] = 15;
	a224 = 32;
	a172 = 6;
	a295 = 9;
	a81 = 4;
	a139 = 36;
	a336 = 0;
	a151 = 0;
	a196 = 16;
	a132 = 0;
	a129 = 14;
	a102 = 14;
	a79[0] = 6;
	a79[1] = 7;
	a79[2] = 8;
	a79[3] = 9;
	a79[4] = 10;
	a79[5] = 11;
	a79[6] = 12;
	a79[7] = 13;
	a320 = 7;
	a221 = 0;
	a303[0] = 42;
	a303[1] = 43;
	a303[2] = 44;
	a303[3] = 45;
	a303[4] = 46;
	a303[5] = 47;
	a293[0] = 48;
	a293[1] = 49;
	a293[2] = 50;
	a293[3] = 51;
	a293[4] = 52;
	a293[5] = 53;
	a376[0] = 54;
	a376[1] = 55;
	a376[2] = 56;
	a376[3] = 57;
	a376[4] = 58;
	a376[5] = 59;
	a265 = a293;
	a212[0] = 78;
	a212[1] = 79;
	a212[2] = 80;
	a212[3] = 81;
	a212[4] = 82;
	a212[5] = 83;
	a384[0] = 84;
	a384[1] = 85;
	a384[2] = 86;
	a384[3] = 87;
	a384[4] = 88;
	a384[5] = 89;
	a362[0] = 90;
	a362[1] = 91;
	a362[2] = 92;
	a362[3] = 93;
	a362[4] = 94;
	a362[5] = 95;
	a296 = a384;
	a324 = 9;
	a260 = 0;
	a232[0] = 8;
	a232[1] = 9;
	a232[2] = 10;
	a232[3] = 11;
	a232[4] = 12;
	a232[5] = 13;
	a232[6] = 14;
	a232[7] = 15;
	a123 = 1;
	a217[0] = 9;
	a217[1] = 10;
	a217[2] = 11;
	a217[3] = 12;
	a217[4] = 13;
	a217[5] = 14;
	a217[6] = 15;
	a217[7] = 16;
	a216[0] = 7;
	a216[1] = 8;
	a216[2] = 9;
	a216[3] = 10;
	a216[4] = 11;
	a216[5] = 12;
	a216[6] = 13;
	a216[7] = 14;
	a142 = 0;
	a398 = 11;
	a125 = 12;
	a141 = 12;
	a326[0] = 2;
	a326[1] = 3;
	a326[2] = 4;
	a326[3] = 5;
	a326[4] = 6;
	a326[5] = 7;
	a326[6] = 8;
	a326[7] = 9;
	a242[0] = 31;
	a242[1] = 32;
	a242[2] = 33;
	a242[3] = 34;
	a242[4] = 35;
	a242[5] = 36;
	a299[0] = 37;
	a299[1] = 38;
	a299[2] = 39;
	a299[3] = 40;
	a299[4] = 41;
	a299[5] = 42;
	a268[0] = 43;
	a268[1] = 44;
	a268[2] = 45;
	a268[3] = 46;
	a268[4] = 47;
	a268[5] = 48;
	a239 = a299;
	a87[0] = 4;
	a87[1] = 5;
	a87[2] = 6;
	a87[3] = 7;
	a87[4] = 8;
	a87[5] = 9;
	a87[6] = 10;
	a87[7] = 11;
	a115[0] = 4;
	a115[1] = 5;
	a115[2] = 6;
	a115[3] = 7;
	a115[4] = 8;
	a115[5] = 9;
	a115[6] = 10;
	a115[7] = 11;
	a130 = 127;
	a170 = 72;
	a378 = 0;
	a148[0] = 21;
	a148[1] = 22;
	a148[2] = 23;
	a148[3] = 24;
	a148[4] = 25;
	a148[5] = 26;
	a119[0] = 27;
	a119[1] = 28;
	a119[2] = 29;
	a119[3] = 30;
	a119[4] = 31;
	a119[5] = 32;
	a18[0] = 33;
	a18[1] = 34;
	a18[2] = 35;
	a18[3] = 36;
	a18[4] = 37;
	a18[5] = 38;
	a46 = a18;
	a253[0] = 96;
	a253[1] = 97;
	a253[2] = 98;
	a253[3] = 99;
	a253[4] = 100;
	a253[5] = 101;
	a289[0] = 102;
	a289[1] = 103;
	a289[2] = 104;
	a289[3] = 105;
	a289[4] = 106;
	a289[5] = 107;
	a250[0] = 108;
	a250[1] = 109;
	a250[2] = 110;
	a250[3] = 111;
	a250[4] = 112;
	a250[5] = 113;
	a276 = a289;
	a1 = 6;
	a97 = 0;
	a234 = 8;
	a310 = 187;
	a36 = 306;
	a245[0] = 9;
	a245[1] = 10;
	a245[2] = 11;
	a245[3] = 12;
	a245[4] = 13;
	a245[5] = 14;
	a354[0] = 15;
	a354[1] = 16;
	a354[2] = 17;
	a354[3] = 18;
	a354[4] = 19;
	a354[5] = 20;
	a290[0] = 21;
	a290[1] = 22;
	a290[2] = 23;
	a290[3] = 24;
	a290[4] = 25;
	a290[5] = 26;
	a274 = a245;
	a30[0] = 5;
	a30[1] = 6;
	a30[2] = 7;
	a30[3] = 8;
	a30[4] = 9;
	a30[5] = 10;
	a30[6] = 11;
	a30[7] = 12;
	a397 = 11;
	a191 = 14;
	a146 = 1;
	a300 = 0;
	a307 = 3;
	a286 = 3;
	a383 = 5;
	a111[0] = 44;
	a111[1] = 45;
	a111[2] = 46;
	a111[3] = 47;
	a111[4] = 48;
	a111[5] = 49;
	a60[0] = 50;
	a60[1] = 51;
	a60[2] = 52;
	a60[3] = 53;
	a60[4] = 54;
	a60[5] = 55;
	a188[0] = 56;
	a188[1] = 57;
	a188[2] = 58;
	a188[3] = 59;
	a188[4] = 60;
	a188[5] = 61;
	a197 = a60;
	a205[0] = 5;
	a205[1] = 6;
	a205[2] = 7;
	a205[3] = 8;
	a205[4] = 9;
	a205[5] = 10;
	a205[6] = 11;
	a205[7] = 12;
	a270 = 11;
	a237 = 4;
	a302 = 11;
	a69 = 32;
	a211 = 2;
	a53 = 116;
	a278 = 8;
	a91 = 9;
	a128 = 10;
	a240 = 0;
	a173 = 32;
	a13 = 338;
	a42 = 2;
	a136 = 7;
	a26[0] = 4;
	a26[1] = 5;
	a26[2] = 6;
	a26[3] = 7;
	a26[4] = 8;
	a26[5] = 9;
	a26[6] = 10;
	a26[7] = 11;
	a134 = 1;
	a373 = 0;
	a72 = 93;
	a382 = -46;
	a152[0] = 6;
	a152[1] = 7;
	a152[2] = 8;
	a152[3] = 9;
	a152[4] = 10;
	a152[5] = 11;
	a144[0] = 12;
	a144[1] = 13;
	a144[2] = 14;
	a144[3] = 15;
	a144[4] = 16;
	a144[5] = 17;
	a153[0] = 18;
	a153[1] = 19;
	a153[2] = 20;
	a153[3] = 21;
	a153[4] = 22;
	a153[5] = 23;
	a39 = a153;
	a249 = 346;
	a179 = -10;
	a154 = 13;
	a135 = 35;
	a225 = 6;
	a200 = 9;
	a167[0] = 2;
	a167[1] = 3;
	a167[2] = 4;
	a167[3] = 5;
	a167[4] = 6;
	a167[5] = 7;
	a167[6] = 8;
	a167[7] = 9;
	a207 = 32;
	a37[0] = 7;
	a37[1] = 8;
	a37[2] = 9;
	a37[3] = 10;
	a37[4] = 11;
	a37[5] = 12;
	a37[6] = 13;
	a37[7] = 14;
	a77 = 12;
	a99 = 5;
	a333 = -26;
	a171 = 33;
	a75 = 32;
	a14 = 8;
	a230 = 4;
	a244 = 11;
	a208[0] = 34;
	a208[1] = 35;
	a208[2] = 36;
	a208[3] = 37;
	a208[4] = 38;
	a208[5] = 39;
	a257[0] = 40;
	a257[1] = 41;
	a257[2] = 42;
	a257[3] = 43;
	a257[4] = 44;
	a257[5] = 45;
	a304[0] = 46;
	a304[1] = 47;
	a304[2] = 48;
	a304[3] = 49;
	a304[4] = 50;
	a304[5] = 51;
	a392 = a257;
	a357 = -187;
	a109[0] = 45;
	a109[1] = 46;
	a109[2] = 47;
	a109[3] = 48;
	a109[4] = 49;
	a109[5] = 50;
	a193[0] = 51;
	a193[1] = 52;
	a193[2] = 53;
	a193[3] = 54;
	a193[4] = 55;
	a193[5] = 56;
	a114[0] = 57;
	a114[1] = 58;
	a114[2] = 59;
	a114[3] = 60;
	a114[4] = 61;
	a114[5] = 62;
	a3 = a109;
	a277 = 85;
	a57 = 14;
	a338 = 4;
	a105 = 36;
	a361 = 32;
	a395 = 0;
	a19 = 254;
	a143 = 35;
	a17 = 257;
	a294[0] = 2;
	a294[1] = 3;
	a294[2] = 4;
	a294[3] = 5;
	a294[4] = 6;
	a294[5] = 7;
	a294[6] = 8;
	a294[7] = 9;
	a7 = 1;
	a313 = 32;
	a64 = 0;
	a318[0] = 22;
	a318[1] = 23;
	a318[2] = 24;
	a318[3] = 25;
	a318[4] = 26;
	a318[5] = 27;
	a285[0] = 28;
	a285[1] = 29;
	a285[2] = 30;
	a285[3] = 31;
	a285[4] = 32;
	a285[5] = 33;
	a311[0] = 34;
	a311[1] = 35;
	a311[2] = 36;
	a311[3] = 37;
	a311[4] = 38;
	a311[5] = 39;
	a370 = a285;
	a158 = 5;
	a218 = 32;
	a366[0] = 7;
	a366[1] = 8;
	a366[2] = 9;
	a366[3] = 10;
	a366[4] = 11;
	a366[5] = 12;
	a366[6] = 13;
	a366[7] = 14;
	a107 = 33;
	a44 = 33;
	a256 = 32;
	a346[0] = 10;
	a346[1] = 11;
	a346[2] = 12;
	a346[3] = 13;
	a346[4] = 14;
	a346[5] = 15;
	a346[6] = 16;
	a346[7] = 17;
	a227[0] = 2;
	a227[1] = 3;
	a227[2] = 4;
	a227[3] = 5;
	a227[4] = 6;
	a227[5] = 7;
	a227[6] = 8;
	a227[7] = 9;
	a202 = 10;
	a47[0] = 8;
	a47[1] = 9;
	a47[2] = 10;
	a47[3] = 11;
	a47[4] = 12;
	a47[5] = 13;
	a47[6] = 14;
	a47[7] = 15;
	a210 = 0;
	a184 = 14;
	a20[0] = 76;
	a20[1] = 77;
	a20[2] = 78;
	a20[3] = 79;
	a20[4] = 80;
	a20[5] = 81;
	a58[0] = 82;
	a58[1] = 83;
	a58[2] = 84;
	a58[3] = 85;
	a58[4] = 86;
	a58[5] = 87;
	a85[0] = 88;
	a85[1] = 89;
	a85[2] = 90;
	a85[3] = 91;
	a85[4] = 92;
	a85[5] = 93;
	a195 = a58;
	a226[0] = 4;
	a226[1] = 5;
	a226[2] = 6;
	a226[3] = 7;
	a226[4] = 8;
	a226[5] = 9;
	a226[6] = 10;
	a226[7] = 11;
	a68[0] = 5;
	a68[1] = 6;
	a68[2] = 7;
	a68[3] = 8;
	a68[4] = 9;
	a68[5] = 10;
	a199[0] = 11;
	a199[1] = 12;
	a199[2] = 13;
	a199[3] = 14;
	a199[4] = 15;
	a199[5] = 16;
	a76[0] = 17;
	a76[1] = 18;
	a76[2] = 19;
	a76[3] = 20;
	a76[4] = 21;
	a76[5] = 22;
	a25 = a68;
	a229[0] = 44;
	a229[1] = 45;
	a229[2] = 46;
	a229[3] = 47;
	a229[4] = 48;
	a229[5] = 49;
	a264[0] = 50;
	a264[1] = 51;
	a264[2] = 52;
	a264[3] = 53;
	a264[4] = 54;
	a264[5] = 55;
	a292[0] = 56;
	a292[1] = 57;
	a292[2] = 58;
	a292[3] = 59;
	a292[4] = 60;
	a292[5] = 61;
	a228 = a264;
	a175[0] = 1;
	a175[1] = 2;
	a175[2] = 3;
	a175[3] = 4;
	a175[4] = 5;
	a175[5] = 6;
	a175[6] = 7;
	a175[7] = 8;
	a177 = 32;
	a120 = 1;
	a131 = -15;
	a164 = 1;
	a122 = 3;
	a165 = 1;
	a89 = 1;
	a174 = 1;
	a63 = 3;
	a12 = 1;
	a67 = 0;
	a169 = 2;
	a133 = 1;
	a35 = 1;
	a50 = 1;
	a98 = 1;
	a162 = 2;
	a56 = -15;
	a178 = 1;
	a5 = 3;
	a90 = 1;
	a110 = -15;
	a51 = 1;
	a156 = -15;
	a93 = -15;
	a181 = 1;
	a94 = 1;
	a31 = 1;
	a88 = -15;
	a161 = 3;
	a168 = 1;
}

void errorCheck() {
	if ((((a1 == a87[0] && a77 == 10) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(0); return;
	}
	if ((((a42 == 1 && a141 == a47[1]) && a173 == 36) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(1); return;
	}
	if ((((a14 == a79[4] && a143 == 32) && a57 == 11) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(2); return;
	}
	if ((((a141 == a47[1] && a72 <= -104) && a57 == 15) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(3); return;
	}
	if ((((a71 == a175[1] && a134 != 1) && a57 == 14) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(4); return;
	}
	if ((((a99 == a26[0] && a172 == 7) && a173 == 34) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(5); return;
	}
	if (((((22 == a25[5]) && (63 == a40[3])) && a57 == 17) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(6); return;
	}
	if ((((a66 != 1 && ((134 < a130) && (276 >= a130))) && a173 == 33) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(7); return;
	}
	if ((((a210 == 1 && a125 == a30[2]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(8); return;
	}
	if ((((325 < a13 && 493 < a130) && a173 == 33) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(9); return;
	}
	if ((((a136 == 12 && a77 == 5) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(10); return;
	}
	if ((((a17 <= 134 && 258 < a72) && a57 == 15) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(11); return;
	}
	if ((((a129 == a92[3] && a172 == 1) && a173 == 34) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(12); return;
	}
	if ((((a1 == a87[4] && a91 == 11) && a173 == 35) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(13); return;
	}
	if ((((a129 == a92[0] && a196 == 10) && a134 == 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(14); return;
	}
	if ((((a129 == a92[1] && a125 == a30[7]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(15); return;
	}
	if ((((a183 == 36 && a278 == a326[5]) && a57 == 16) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(16); return;
	}
	if ((((a129 == a92[5] && a77 == 12) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(17); return;
	}
	if ((((a69 == 36 && a143 == 36) && a57 == 11) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(18); return;
	}
	if ((((a155 == 35 && a77 == 7) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(19); return;
	}
	if ((((a13 <= -10 && a158 == 7) && a57 == 10) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(20); return;
	}
	if ((((a54 <= 164 && a196 == 12) && a134 == 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(21); return;
	}
	if ((((a129 == a92[3] && a77 == 12) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(22); return;
	}
	if ((((a196 == 11 && a295 == a366[0]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(23); return;
	}
	if ((((a1 == a87[3] && a91 == 11) && a173 == 35) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(24); return;
	}
	if ((((a105 == 35 && a158 == 6) && a57 == 10) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(25); return;
	}
	if (((((9 == a274[0]) && a172 == 4) && a173 == 34) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(26); return;
	}
	if ((((a184 == a157[3] && a295 == a366[4]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(27); return;
	}
	if ((((a7 != 1 && a172 == 6) && a173 == 34) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(28); return;
	}
	if ((((a8 == 6 && a172 == 2) && a173 == 34) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(29); return;
	}
	if (((((15 == a39[3]) && a73 <= 167) && a146 != 1) && a75 == 36)) {
		cf = 0;
		__VERIFIER_error(30); return;
	}
	if ((((a244 == a363[0] && a141 == a47[2]) && a173 == 36) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(31); return;
	}
	if ((((a81 == a167[5] && a125 == a30[5]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(32); return;
	}
	if ((((((-58 < a179) && (23 >= a179)) && a81 == a167[4]) && a57 == 12) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(33); return;
	}
	if ((((a69 == 32 && a143 == 36) && a57 == 11) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(34); return;
	}
	if ((((((277 < a36) && (307 >= a36)) && ((-104 < a72) && (100 >= a72))) && a57 == 15) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(35); return;
	}
	if ((((a141 == a47[2] && a72 <= -104) && a57 == 15) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(36); return;
	}
	if ((((a136 == 5 && a77 == 5) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(37); return;
	}
	if ((((a81 == a167[5] && a278 == a326[7]) && a57 == 16) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(38); return;
	}
	if ((((a81 == a167[0] && a125 == a30[5]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(39); return;
	}
	if ((((a173 == 32 && a143 == 34) && a57 == 11) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(40); return;
	}
	if ((((a105 == 36 && a158 == 6) && a57 == 10) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(41); return;
	}
	if ((((a81 == a167[5] && a158 == 4) && a57 == 10) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(42); return;
	}
	if ((((a141 == a47[7] && a72 <= -104) && a57 == 15) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(43); return;
	}
	if ((((a69 == 35 && a143 == 36) && a57 == 11) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(44); return;
	}
	if ((((a143 == 34 && a295 == a366[6]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(45); return;
	}
	if ((((a158 == 8 && a81 == a167[2]) && a57 == 12) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(46); return;
	}
	if ((((a99 == a26[1] && a81 == a167[0]) && a57 == 12) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(47); return;
	}
	if ((((a177 == 34 && (26 == a137[1])) && a132 == 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(48); return;
	}
	if ((((a81 == a167[6] && a125 == a30[5]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(49); return;
	}
	if ((((a16 != 1 && ((167 < a73) && (277 >= a73))) && a146 != 1) && a75 == 36)) {
		cf = 0;
		__VERIFIER_error(50); return;
	}
	if ((((a184 == a157[5] && a295 == a366[4]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(51); return;
	}
	if ((((176 < a53 && a295 == a366[5]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(52); return;
	}
	if ((((a128 == 6 && a141 == a47[6]) && a173 == 36) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(53); return;
	}
	if ((((((26 < a170) && (82 >= a170)) && a81 == a167[5]) && a57 == 12) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(54); return;
	}
	if (((((5 == a25[0]) && (63 == a40[3])) && a57 == 17) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(55); return;
	}
	if (((((23 == a274[2]) && a172 == 4) && a173 == 34) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(56); return;
	}
	if ((((a200 == a115[6] && a158 == 5) && a57 == 10) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(57); return;
	}
	if ((((a155 == 32 && a77 == 7) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(58); return;
	}
	if ((((a44 == 32 && a77 == 8) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(59); return;
	}
	if ((((((306 < a19) && (405 >= a19)) && a278 == a326[0]) && a57 == 16) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(60); return;
	}
	if ((((a129 == a92[7] && a196 == 10) && a134 == 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(61); return;
	}
	if ((((a69 == 34 && a143 == 36) && a57 == 11) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(62); return;
	}
	if ((((a139 == 33 && ((276 < a130) && (493 >= a130))) && a173 == 33) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(63); return;
	}
	if ((((a64 != 1 && 402 < a73) && a146 != 1) && a75 == 36)) {
		cf = 0;
		__VERIFIER_error(64); return;
	}
	if ((((a141 == a47[5] && a72 <= -104) && a57 == 15) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(65); return;
	}
	if ((((a179 <= -162 && a81 == a167[4]) && a57 == 12) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(66); return;
	}
	if ((((a99 == a26[2] && a81 == a167[0]) && a57 == 12) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(67); return;
	}
	if ((((a141 == a47[0] && a72 <= -104) && a57 == 15) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(68); return;
	}
	if ((((a170 <= 26 && a295 == a366[3]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(69); return;
	}
	if ((((a81 == a167[3] && a158 == 8) && a57 == 10) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(70); return;
	}
	if (((((55 == a40[1]) && a278 == a326[2]) && a57 == 16) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(71); return;
	}
	if ((((a183 == 35 && a278 == a326[5]) && a57 == 16) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(72); return;
	}
	if ((((a1 == a87[3] && a77 == 10) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(73); return;
	}
	if ((((a210 == 1 && a143 == 35) && a57 == 11) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(74); return;
	}
	if (((((86 == a195[4]) && a91 == 13) && a173 == 35) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(75); return;
	}
	if ((((a107 == 32 && a278 == a326[4]) && a57 == 16) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(76); return;
	}
	if ((((a141 == a47[6] && (55 == a40[1])) && a57 == 17) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(77); return;
	}
	if (((((60 == a3[3]) && a158 == 9) && a57 == 10) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(78); return;
	}
	if ((((a191 == a37[5] && a130 <= 134) && a173 == 33) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(79); return;
	}
	if ((((a81 == a167[3] && a125 == a30[5]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(80); return;
	}
	if (((((45 == a197[1]) && a81 == a167[1]) && a57 == 12) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(81); return;
	}
	if ((((a155 == 34 && a77 == 7) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(82); return;
	}
	if ((((a1 == a87[2] && a77 == 10) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(83); return;
	}
	if ((((a196 == 13 && a295 == a366[0]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(84); return;
	}
	if ((((a107 == 34 && a172 == 8) && a173 == 34) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(85); return;
	}
	if ((((a123 == 1 && (31 == a137[0])) && a132 == 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(86); return;
	}
	if ((((a8 == 12 && a125 == a30[1]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(87); return;
	}
	if (((((6 == a39[0]) && a73 <= 167) && a146 != 1) && a75 == 36)) {
		cf = 0;
		__VERIFIER_error(88); return;
	}
	if ((((((-46 < a53) && (74 >= a53)) && a295 == a366[5]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(89); return;
	}
	if ((((a134 == 1 && a278 == a326[6]) && a57 == 16) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(90); return;
	}
	if ((((a42 == 7 && a141 == a47[1]) && a173 == 36) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(91); return;
	}
	if ((((((82 < a170) && (121 >= a170)) && a295 == a366[3]) && a134 != 1) && a75 == 35)) {
		cf = 0;
		__VERIFIER_error(92); return;
	}
	if ((((a99 == a26[3] && a77 == 11) && a132 != 1) && a75 == 33)) {
		cf = 0;
		__VERIFIER_error(93); return;
	}
	if ((((a139 == 35 && ((276 < a130) && (493 >= a130))) && a173 == 33) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(94); return;
	}
	if ((((a397 == 11 && a125 == a30[3]) && a173 == 32) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(95); return;
	}
	if ((((a184 == a157[2] && a141 == a47[3]) && a173 == 36) && a75 == 32)) {
		cf = 0;
		__VERIFIER_error(96); return;
	}
	if ((((a71 == a175[4] && a134 != 1) && a57 == 14) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(97); return;
	}
	if ((((258 < a72 && (21 == a46[0])) && a146 == 1) && a75 == 36)) {
		cf = 0;
		__VERIFIER_error(98); return;
	}
	if ((((a141 == a47[0] && (55 == a40[1])) && a57 == 17) && a75 == 34)) {
		cf = 0;
		__VERIFIER_error(99); return;
	}
}
void calculate_outputm20(int input) {
	if (((a320 == 6 && (26 == a137[1])) && (a202 == a217[0] && (((((a75 == 33 && (a132 == 1 && ((input == inputs[3] && cf == 1) && a177 == 32))) && a218 == 33) && a368 == 1) && a313 == 33) && (47 == a265[5]))))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a67 -= (a67 - 20) < a67 ? 4 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a276 = a250;
		a237 = 7;
		a310 = (((21 - 24207) * 1) + -5378);
		a313 = 33;
		a296 = a212;
		a243 = ((((a243 % 11) + -157) + -4) - -1);
		a295 = a366[((a230 * a270) - 30)];
		a235 = a216[0];
		a270 = 13;
		a373 = 1;
		a286 = a294[2];
		a75 = 35;
		a134 = 0;
		a234 = a372[3];
		a370 = a318;
		a206 = 7;
		a307 = a227[1];
		a196 = 16;
		a207 = 36;
		a240 = 0;
		a249 = (((((a249 % 101) + 254) + -1) / 5) - -130);
		a333 = ((((48 * 10) / 9) - 41) + -5);
		a383 = a226[6];
		a386 = (((94 - 24626) * 1) + 24705);
		a382 = (((((a382 % 12) - 48) - 22186) + -582) + 22764);
		a324 = a232[1];
		a230 = 3;
	}
	if (((input == inputs[9] && (a373 == 1 && (a225 == a205[0] && a260 == 1))) && (a177 == 32 && (((26 == a137[1]) && ((47 == a265[5]) && ((a132 == 1 && (cf == 1 && a75 == 33)) && a395 == 1))) && a383 == a226[0])))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		cf = 0;
		a75 = 34;
		a57 = ((a230 / a338) - -14);
		a72 = (((94 * 5) * 5) + 2414);
		a17 = ((((((a72 * a72) % 14999) - 22025) * 10) / 9) - -3963);
	}
	if ((((a378 == 1 && ((a75 == 33 && a201 <= -199) && (26 == a137[1]))) && a336 == 1) && ((37 == a392[3]) && (a361 == 33 && (a339 == 1 && (a177 == 32 && ((cf == 1 && input == inputs[0]) && a132 == 1))))))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a169 -= (a169 - 20) < a169 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a338 = 7;
		a265 = a303;
		a307 = a227[3];
		a353 = a399;
		a228 = a292;
		a286 = a294[0];
		a107 = 33;
		a395 = 1;
		a392 = a304;
		a240 = 1;
		a370 = a318;
		a201 = (((((a201 % 94) + 93) - -1451) * 1) / 10);
		a296 = a384;
		a270 = 12;
		a249 = (((((a249 % 14750) - -15249) - -1) + -23170) - -23170);
		a260 = 1;
		a361 = 33;
		a313 = 36;
		a320 = 12;
		a339 = 1;
		a324 = a232[6];
		a383 = a226[5];
		a359 = 3;
		a368 = 1;
		a302 = a346[3];
		a234 = a372[0];
		a329 = 36;
		a336 = 0;
		a269 = 35;
		a358 = a348;
		a239 = a268;
		a225 = a205[2];
		a211 = 7;
		a277 = (((a277 + 20397) / 5) + -23039);
		a357 = (((63 + -20909) - 3828) + -1167);
		a373 = 1;
		a382 = ((((a382 % 107) + 115) - -26297) + -26263);
		a75 = 32;
		a224 = 34;
		a202 = a217[2];
		a276 = a253;
		a312 = 35;
		a235 = a216[7];
		a398 = 12;
		a230 = 10;
		a310 = ((((98 / 5) - 9818) * -1) / 10);
		a218 = 34;
		a300 = 1;
		a125 = a30[(a206 - -2)];
		a173 = 32;
		a243 = ((((a243 - -5349) % 14910) - 15088) - 3);
		a256 = 33;
		a206 = 9;
	}
	if (((input == inputs[2] && (a338 == 3 && a243 <= -179)) && (a177 == 32 && ((a224 == 33 && (a313 == 33 && (a75 == 33 && ((81 == a296[3]) && ((26 == a137[1]) && (a132 == 1 && cf == 1)))))) && a234 == a372[0])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a75 = 34;
		a40 = a83;
		a57 = (a398 + 7);
		a25 = a68;
	}
	if (((input == inputs[8] && (a249 <= 152 && (a324 == a232[0] && (a75 == 33 && ((cf == 1 && a177 == 32) && a132 == 1))))) && ((((3 == a353[2]) && ((24 == a370[2]) && a378 == 1)) && a307 == a227[0]) && (26 == a137[1])))) {
		a164 += (a164 + 20) > a164 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		cf = 0;
		a57 = (a320 + 10);
		a75 = 34;
		a278 = a326[(a270 + -10)];
		a19 = ((((91 - -3835) - -23987) + 1979) + -29503);
	}
	if (((a382 <= -65 && (a202 == a217[0] && ((((input == inputs[5] && a361 == 33) && a359 == 3) && a75 == 33) && a132 == 1))) && (a277 <= -10 && (((a177 == 32 && cf == 1) && (26 == a137[1])) && a312 == 33)))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a35 -= (a35 - 20) < a35 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		if (((!(a320 == 12) || (!(a143 == 36) && (a134 == 1 && a146 == 1))) && !(a177 == 34))) {
			a146 = 0;
			a75 = 36;
			a16 = 0;
			a73 = (((34 + 175) * 5) / 5);
		} else {
			a170 = ((((((a201 * a249) % 14999) / 5) - 2558) / 5) - 14824);
			a134 = 0;
			a75 = 35;
			a295 = a366[((a211 + a338) - 1)];
		}
	}
	if (((input == inputs[4] && (((a218 == 33 && ((a201 <= -199 && a249 <= 152) && a75 == 33)) && a132 == 1) && a395 == 1)) && ((a359 == 3 && ((26 == a137[1]) && (a177 == 32 && cf == 1))) && a260 == 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a169 -= (a169 - 20) < a169 ? 4 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if ((178 < a201 && ((a333 <= -47 && !(55 == a40[1])) || !(a307 == a227[3])))) {
			a225 = a205[7];
			a201 = (((((a201 % 14900) - 199) - 14263) + 26038) + -22726);
			a353 = a263;
			a370 = a285;
			a237 = 9;
			a57 = ((a270 / a206) + 10);
			a256 = 35;
			a249 = ((((a249 - 0) / 5) % 101) + 254);
			a296 = a212;
			a75 = 34;
			a313 = 32;
			a324 = a232[0];
			a382 = ((((a382 % 14911) + 15087) - -4378) - -5003);
			a329 = 36;
			a207 = 34;
			a277 = ((((a277 % 14830) - -15169) - -12115) / 5);
			a228 = a229;
			a378 = 0;
			a386 = (((52 - -140) - 25948) + 25841);
			a373 = 0;
			a398 = 14;
			a270 = 16;
			a269 = 33;
			a339 = 1;
			a211 = 2;
			a235 = a216[3];
			a224 = 32;
			a265 = a293;
			a368 = 0;
			a333 = (((3 / 5) - -3707) * 5);
			a320 = 7;
			a240 = 0;
			a336 = 0;
			a358 = a348;
			a338 = 4;
			a230 = 6;
			a361 = 33;
			a206 = 11;
			a395 = 1;
			a260 = 1;
			a234 = a372[2];
			a312 = 33;
			a81 = a167[(a359 + -1)];
			a307 = a227[5];
			a218 = 33;
			a392 = a208;
			a383 = a226[3];
			a158 = ((a57 / a57) - -4);
			a239 = a299;
			a243 = ((((a243 % 14910) + -179) * 1) - 4354);
			a359 = 3;
		} else {
			a260 = 1;
			a207 = 33;
			a336 = 0;
			a312 = 35;
			a239 = a299;
			a353 = a241;
			a398 = 10;
			a378 = 0;
			a57 = 12;
			a211 = 6;
			a333 = (((39 + 26488) / 5) - 5159);
			a228 = a264;
			a368 = 0;
			a359 = 8;
			a243 = ((((a243 / -5) - 27808) + 19465) * -3);
			a202 = a217[0];
			a206 = 5;
			a218 = 36;
			a329 = 33;
			a235 = a216[3];
			a237 = 4;
			a224 = 35;
			a201 = ((((((a201 % 14900) + -199) * 1) - -25366) * -1) / 10);
			a324 = a232[1];
			a81 = a167[(a57 - 5)];
			a358 = a351;
			a386 = (((81 - -27546) / 5) + 1048);
			a338 = 9;
			a392 = a304;
			a270 = 14;
			a240 = 0;
			a249 = ((((a249 % 14750) - -15249) - -1) * 1);
			a339 = 1;
			a75 = 34;
			a382 = ((((a382 - 0) % 14967) - 65) - 7499);
			a225 = a205[6];
			a361 = 32;
			a370 = a318;
			a296 = a212;
			a269 = 36;
			a230 = 9;
			a395 = 1;
			a307 = a227[5];
			a277 = ((((a277 % 14995) - 10) + -3277) + -6232);
			a323 = (a57 + -3);
		}
	}
	if ((((a359 == 3 && ((((a132 == 1 && ((26 == a137[1]) && cf == 1)) && input == inputs[1]) && a177 == 32) && a234 == a372[0])) && a201 <= -199) && ((((67 == a358[2]) && a75 == 33) && a395 == 1) && a324 == a232[0]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a178 += (a178 + 20) > a178 ? 4 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		a77 = ((a359 - a206) - -6);
		a132 = 0;
		a136 = a77;
	}
	if (((a329 == 33 && ((a256 == 33 && (a240 == 1 && (a249 <= 152 && (26 == a137[1])))) && a211 == 1)) && ((24 == a370[2]) && ((input == inputs[7] && ((a75 == 33 && cf == 1) && a132 == 1)) && a177 == 32)))) {
		a164 += (a164 + 20) > a164 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		if (a368 == 1) {
			a353 = a241;
			a378 = 1;
			a269 = 36;
			a398 = 13;
			a256 = 35;
			a75 = 32;
			a333 = ((((73 + -44) / 5) - -20578) + -20459);
			a395 = 1;
			a329 = 33;
			a206 = 8;
			a310 = ((((38 - -13771) - 13486) - 14022) + 14022);
			a338 = 7;
			a276 = a253;
			a373 = 0;
			a300 = 0;
			a228 = a264;
			a307 = a227[2];
			a201 = (((((a201 % 14900) + -199) * 10) / 9) - 11958);
			a237 = 5;
			a230 = 10;
			a313 = 34;
			a392 = a304;
			a286 = a294[4];
			a277 = (((((a277 % 14995) + -10) * 10) / 9) - 11159);
			a224 = 34;
			a42 = (a320 + 2);
			a239 = a299;
			a312 = 32;
			a234 = a372[4];
			a141 = a47[(a359 - 2)];
			a357 = (((25 - 24868) - -24822) - 19);
			a211 = 4;
			a260 = 1;
			a218 = 35;
			a173 = 36;
			a225 = a205[1];
			a240 = 1;
			a320 = 6;
			a383 = a226[2];
			a270 = 15;
			a324 = a232[5];
			a359 = 9;
		} else {
			a386 = ((((94 + -29583) + 21864) * -1) / 10);
			a256 = 35;
			a395 = 1;
			a276 = a250;
			a307 = a227[2];
			a134 = 1;
			a333 = (((((29 - -5647) * 10) / 9) * 10) / 9);
			a357 = (((98 - -12406) * 2) + -25008);
			a378 = 1;
			a224 = 34;
			a329 = 34;
			a310 = (((((73 - -12756) + -20474) / 5) * -3) / 10);
			a237 = 9;
			a207 = 32;
			a201 = ((((a201 - 0) % 14900) + -199) * 1);
			a392 = a304;
			a286 = a294[5];
			a324 = a232[5];
			a75 = 35;
			a196 = 10;
			a129 = a92[(a196 - 8)];
		}
	}
	if (((((a269 == 33 && ((a202 == a217[0] && (a320 == 6 && (a202 == a217[0] && a359 == 3))) && a132 == 1)) && (26 == a137[1])) && input == inputs[6]) && (a359 == 3 && (a177 == 32 && (a75 == 33 && cf == 1))))) {
		a164 += (a164 + 20) > a164 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a75 = 32;
		a173 = 33;
		a130 = (((35 * 5) - -13355) - -12833);
		a13 = (((((a130 * a130) % 14999) - -1643) - -2410) * 1);
	}
}
void calculate_outputm1(int input) {
	if ((((a235 == a216[0] && a243 <= -179) && a383 == a226[0]) && (a312 == 33 && (a286 == a294[0] && ((cf == 1 && (26 == a137[1])) && a324 == a232[0]))))) {
		if (((((36 == a239[5]) && (a269 == 33 && a256 == 33)) && a395 == 1) && ((67 == a358[2]) && ((a177 == 32 && cf == 1) && (45 == a228[1]))))) {
			calculate_outputm20(input);
		}
	}
}
void calculate_outputm29(int input) {
	if (((a270 == 10 && (a235 == a216[0] && (a75 == 33 && (input == inputs[5] && (a77 == 8 && (cf == 1 && a132 != 1)))))) && (a235 == a216[0] && (((a361 == 33 && a357 <= -188) && a44 == 34) && (36 == a239[5]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a370 = a318;
		a310 = ((((a310 - 0) % 15080) - 14919) - 1);
		a286 = a294[3];
		a270 = 16;
		a206 = 10;
		a234 = a372[1];
		a249 = ((((a249 * 1) % 14750) + 15249) - -1);
		a329 = 36;
		a75 = 35;
		a382 = ((((a382 - -5487) - 2157) % 14911) - -15087);
		a235 = a216[4];
		a240 = 0;
		a307 = a227[6];
		a373 = 1;
		a296 = a384;
		a134 = 0;
		a357 = (((((a357 + 0) * 1) * 1) * -2) / 10);
		a313 = 32;
		a324 = a232[1];
		a237 = 6;
		a383 = a226[3];
		a398 = 11;
		a300 = 0;
		a302 = a346[5];
		a196 = ((a359 + a359) + 10);
		a207 = 33;
		a243 = ((((99 + -265) * 5) - -27325) - 26671);
		a230 = 7;
		a295 = a366[(a196 - 16)];
	}
	if ((((a235 == a216[0] && ((a44 == 34 && (a338 == 3 && a211 == 1)) && a132 != 1)) && (37 == a392[3])) && (a224 == 33 && (a395 == 1 && (a75 == 33 && (input == inputs[6] && (cf == 1 && a77 == 8))))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a134 = 0;
		a75 = 35;
		a184 = a157[(a77 + -5)];
		a295 = a366[(a77 - 4)];
	}
	if (((((98 == a276[2]) && (((a75 == 33 && cf == 1) && input == inputs[2]) && (45 == a228[1]))) && a201 <= -199) && (((((a386 <= 77 && a77 == 8) && a132 != 1) && a324 == a232[0]) && a44 == 34) && a256 == 33))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		if (cf == 1) {
			a75 = 35;
			a134 = 0;
			a295 = a366[((a211 + a206) - 1)];
			a184 = a157[((a77 / a77) + 2)];
		} else {
			a155 = 32;
			a77 = (a359 - -4);
		}
	}
	if (((a320 == 6 && ((((((cf == 1 && a44 == 34) && a75 == 33) && a240 == 1) && a383 == a226[0]) && a132 != 1) && input == inputs[4])) && (a249 <= 152 && ((a339 == 1 && a277 <= -10) && a77 == 8)))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if ((!(a312 == 34) && a134 == 1)) {
			a353 = a399;
			a286 = a294[6];
			a307 = a227[7];
			a338 = 7;
			a265 = a303;
			a211 = 4;
			a102 = a127[((a77 / a77) + 4)];
			a296 = a384;
			a386 = ((((a386 % 61) + 262) + 0) + 0);
			a392 = a304;
			a201 = ((((a201 * -9) / 10) * 1) + 2004);
			a256 = 34;
			a202 = a217[4];
			a368 = 1;
			a373 = 1;
			a91 = ((a237 - a230) + 8);
			a225 = a205[7];
			a235 = a216[2];
			a243 = ((((45 + 9004) + -9133) - -2713) + -2710);
			a357 = ((((a357 / 5) / 5) / 5) + 21511);
			a378 = 1;
			a277 = (((((a277 * 1) - 0) - -26733) % 14995) - 15004);
			a207 = 35;
			a358 = a348;
			a218 = 33;
			a361 = 36;
			a260 = 1;
			a240 = 1;
			a339 = 1;
			a382 = ((((a382 * 1) % 14967) - 65) * 1);
			a173 = 35;
			a336 = 1;
			a239 = a299;
			a370 = a318;
			a269 = 34;
			a249 = ((((a249 % 14750) - -15249) - 0) * 1);
			a230 = 9;
			a313 = 35;
			a75 = 32;
			a383 = a226[3];
			a228 = a292;
			a224 = 35;
			a270 = 10;
			a320 = 13;
			a310 = ((((a310 - 0) - -20950) % 15080) - 14919);
			a302 = a346[3];
			a395 = 1;
			a359 = 6;
			a333 = ((((74 + 4991) * 10) / 9) - -8579);
			a206 = 9;
			a276 = a289;
			a237 = 7;
		} else {
			a278 = a326[((a270 - a77) - 2)];
			a75 = 34;
			a19 = ((((63 - -245) / 5) * 55) / 10);
			a57 = ((a77 / a359) - -14);
		}
	}
	if (((a373 == 1 && (a44 == 34 && (a368 == 1 && ((47 == a265[5]) && (((a77 == 8 && cf == 1) && input == inputs[7]) && a75 == 33))))) && ((a395 == 1 && (a132 != 1 && (24 == a370[2]))) && a302 == a346[0]))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		a168 -= (a168 - 20) < a168 ? 1 : 0;
		cf = 0;
		if (a64 == 1) {
			a249 = (((((a249 + 0) + 0) - 0) % 101) + 253);
			a207 = 35;
			a383 = a226[0];
			a300 = 0;
			a373 = 1;
			a201 = (((((a201 + 16904) % 93) + -104) + 15673) - 15673);
			a310 = (((((a310 / 5) + -3541) - 4829) % 77) + 270);
			a265 = a303;
			a81 = a167[(a230 + -1)];
			a218 = 32;
			a202 = a217[7];
			a228 = a264;
			a361 = 34;
			a378 = 0;
			a276 = a289;
			a358 = a335;
			a398 = 11;
			a260 = 1;
			a313 = 35;
			a296 = a384;
			a307 = a227[3];
			a386 = (((((a386 % 61) + 138) * 5) % 61) + 115);
			a239 = a242;
			a312 = 36;
			a240 = 0;
			a225 = a205[0];
			a336 = 0;
			a243 = (((((83 * 10) / -5) * 1) / 5) - 137);
			a230 = 8;
			a158 = (a206 - -7);
			a333 = ((((20 / 5) + -801) + -12738) + 13663);
			a392 = a257;
			a324 = a232[6];
			a359 = 4;
			a302 = a346[6];
			a357 = (((a357 / 5) - 4255) / 5);
			a256 = 32;
			a211 = 1;
			a75 = 34;
			a224 = 36;
			a339 = 1;
			a235 = a216[6];
			a368 = 0;
			a57 = (a270 - -2);
			a237 = 3;
			a329 = 35;
			a370 = a318;
			a234 = a372[4];
			a338 = 9;
			a277 = (((((a277 % 14995) + -10) / 5) * 10) / 2);
			a382 = (((((a382 - -5362) % 12) + -52) - -26377) + -26376);
			a206 = 11;
			a286 = a294[4];
			a353 = a241;
			a395 = 0;
			a269 = 33;
			a320 = 9;
			a270 = 13;
		} else {
			a125 = a30[(a359 - -2)];
			a173 = 32;
			a75 = 32;
			a81 = a167[a359];
		}
	}
	if (((a310 <= 160 && (((3 == a353[2]) && a201 <= -199) && a230 == 3)) && (a132 != 1 && ((a302 == a346[0] && (a77 == 8 && (input == inputs[8] && (a44 == 34 && (a75 == 33 && cf == 1))))) && a240 == 1)))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a155 = 32;
		a77 = (a237 + 4);
	}
	if ((((((input == inputs[1] && (81 == a296[3])) && (67 == a358[2])) && a132 != 1) && a361 == 33) && (a77 == 8 && ((98 == a276[2]) && ((45 == a228[1]) && (a382 <= -65 && ((a44 == 34 && cf == 1) && a75 == 33))))))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a98 -= (a98 - 20) < a98 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a75 = 34;
		a69 = 34;
		a143 = 36;
		a57 = (a77 + 3);
	}
	if ((((a359 == 3 && (a211 == 1 && a338 == 3)) && a338 == 3) && ((a270 == 10 && (a77 == 8 && (((a44 == 34 && (cf == 1 && a132 != 1)) && a378 == 1) && input == inputs[3]))) && a75 == 33))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 2 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a75 = 32;
		a173 = 33;
		a66 = 0;
		a130 = (((10 + -27931) + 28146) - 26);
	}
	if ((((a269 == 33 && (a339 == 1 && a230 == 3)) && a286 == a294[0]) && ((a211 == 1 && (a77 == 8 && (input == inputs[9] && (a132 != 1 && (a75 == 33 && (a44 == 34 && cf == 1)))))) && a225 == a205[0]))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a237 = 7;
		a398 = 17;
		a300 = 0;
		a333 = (((49 / 5) * 5) - -122);
		a276 = a289;
		a177 = 32;
		a302 = a346[1];
		a207 = 33;
		a386 = ((((a386 % 14837) - -15162) * 1) - -1);
		a132 = 1;
		a310 = (((((a310 % 14821) - -15178) - 9852) + 7889) + 1965);
		a357 = (((((a357 % 65) + -89) / 5) - 11577) - -11521);
		a234 = a372[5];
		a329 = 36;
		a137 = a116;
	}
	if (((((a269 == 33 && ((cf == 1 && a75 == 33) && a44 == 34)) && a211 == 1) && a361 == 33) && ((a338 == 3 && (input == inputs[0] && ((a77 == 8 && a249 <= 152) && a132 != 1))) && a310 <= 160))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a63 -= (a63 - 20) < a63 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a77 = (a237 + 8);
		a99 = a26[(a77 - 8)];
	}
}
void calculate_outputm30(int input) {
	if ((((((a77 == 9 && cf == 1) && a75 == 33) && a260 == 1) && a16 == 1) && (input == inputs[0] && ((a132 != 1 && (a386 <= 77 && (a286 == a294[0] && (a312 == 33 && a395 == 1)))) && a310 <= 160)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		cf = 0;
		a57 = ((a398 / a320) - -16);
		a75 = 34;
		a40 = a65;
		a141 = a47[((a57 + a237) - 20)];
	}
	if (((a260 == 1 && (((a75 == 33 && (a77 == 9 && (cf == 1 && a132 != 1))) && a16 == 1) && a307 == a227[0])) && (a201 <= -199 && ((a395 == 1 && (a211 == 1 && input == inputs[9])) && a313 == 33)))) {
		a164 += (a164 + 20) > a164 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a218 = 35;
		a392 = a257;
		a307 = a227[3];
		a338 = 7;
		a357 = ((((a357 * -2) / 10) - -7884) * 2);
		a75 = 34;
		a361 = 36;
		a57 = (a211 - -11);
		a224 = 35;
		a230 = 10;
		a353 = a241;
		a243 = ((((a243 % 11) + -165) + 1) * 1);
		a206 = 4;
		a249 = ((((a249 * 1) % 14750) - -15249) * 1);
		a378 = 0;
		a81 = a167[((a57 / a77) - -1)];
		a310 = ((((a310 % 15080) - 14919) + -1) + -1);
		a201 = (((((a201 % 14900) - 199) * 10) / 9) + -7917);
		a158 = (a398 + -2);
	}
	if (((((a225 == a205[0] && (a16 == 1 && (cf == 1 && a77 == 9))) && a75 == 33) && a270 == 10) && (a368 == 1 && ((a132 != 1 && ((3 == a353[2]) && (a286 == a294[0] && input == inputs[4]))) && a270 == 10)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a94 += (a94 + 20) > a94 ? 4 : 0;
		cf = 0;
		a361 = 34;
		a256 = 35;
		a211 = 8;
		a91 = (a398 - -1);
		a320 = 10;
		a276 = a253;
		a383 = a226[5];
		a357 = ((((a357 % 38) + 18) - 20973) - -20949);
		a339 = 1;
		a370 = a311;
		a269 = 35;
		a353 = a399;
		a312 = 36;
		a239 = a242;
		a207 = 33;
		a237 = 9;
		a359 = 9;
		a235 = a216[5];
		a307 = a227[2];
		a1 = a87[((a230 - a91) - -14)];
		a395 = 1;
		a228 = a229;
		a313 = 35;
		a386 = ((((a386 - 0) % 14837) - -15162) * 1);
		a249 = ((((a249 * 1) + 18129) % 14750) - -15249);
		a302 = a346[5];
		a270 = 15;
		a218 = 35;
		a392 = a208;
		a201 = (((((a201 % 14900) + -199) / 5) / 5) - 20677);
		a240 = 1;
		a202 = a217[7];
		a338 = 10;
		a225 = a205[4];
		a378 = 1;
		a373 = 1;
		a224 = 35;
		a206 = 10;
		a358 = a348;
		a234 = a372[3];
		a336 = 1;
		a173 = 35;
		a230 = 9;
		a310 = ((((a310 % 15080) + -14919) * 1) + -1);
		a329 = 35;
		a333 = (((((a333 % 14911) + 15088) * 1) - 23363) - -34206);
		a296 = a212;
		a260 = 1;
		a286 = a294[5];
		a243 = (((a243 / 5) - 6617) - 8977);
		a368 = 1;
		a75 = 32;
		a277 = (((70 + 23821) - -2533) + 1144);
		a398 = 10;
	}
	if (((((a339 == 1 && (((a224 == 33 && ((cf == 1 && a132 != 1) && a77 == 9)) && a336 == 1) && a243 <= -179)) && a75 == 33) && input == inputs[5]) && (a218 == 33 && (a16 == 1 && (24 == a370[2]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a174 += (a174 + 20) > a174 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a134 = 1;
		a196 = ((a320 / a230) + 8);
		a75 = 35;
		a129 = a92[(a237 - -4)];
	}
	if (((((a16 == 1 && (a357 <= -188 && a230 == 3)) && a398 == 10) && a249 <= 152) && (a256 == 33 && (((a75 == 33 && ((a77 == 9 && cf == 1) && a132 != 1)) && input == inputs[7]) && a373 == 1)))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a81 = a167[(a211 - -3)];
		a75 = 34;
		a57 = (a206 + 8);
		a179 = ((((60 - 19756) * 1) * 10) / 9);
	}
	if (((input == inputs[3] && (a320 == 6 && (a339 == 1 && (81 == a296[3])))) && ((a338 == 3 && (((a225 == a205[0] && (a132 != 1 && (cf == 1 && a77 == 9))) && a75 == 33) && a16 == 1)) && a218 == 33))) {
		a120 -= (a120 - 20) < a120 ? 2 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a339 = 1;
		a378 = 1;
		a75 = 32;
		a310 = ((((a310 % 15080) - 14919) + -1) + -1);
		a243 = (((a243 + 0) - -29967) - -55);
		a270 = 16;
		a240 = 1;
		a277 = (((64 + 9859) * 3) + 148);
		a173 = 33;
		a392 = a304;
		a269 = 35;
		a225 = a205[6];
		a359 = 10;
		a313 = 33;
		a224 = 35;
		a357 = (((a357 - -30106) + -7172) + 7218);
		a276 = a253;
		a191 = a37[(a77 - 4)];
		a239 = a242;
		a206 = 6;
		a235 = a216[6];
		a130 = (((62 + -5887) - -763) / 5);
	}
	if ((((a206 == 4 && (((a249 <= 152 && input == inputs[1]) && a338 == 3) && a359 == 3)) && (24 == a370[2])) && ((24 == a370[2]) && (a75 == 33 && (a16 == 1 && ((a77 == 9 && cf == 1) && a132 != 1)))))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a67 -= (a67 - 20) < a67 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a57 = (a237 - -9);
		a75 = 34;
		a81 = a167[((a338 + a338) + -6)];
		a99 = a26[(a57 + -10)];
	}
	if (((a361 == 33 && ((a234 == a372[0] && (input == inputs[8] && ((cf == 1 && a132 != 1) && a77 == 9))) && a75 == 33)) && (a16 == 1 && (a357 <= -188 && (a357 <= -188 && (a234 == a372[0] && a202 == a217[0])))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a67 -= (a67 - 20) < a67 ? 4 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		cf = 0;
		a240 = 1;
		a333 = ((((a333 + 18742) % 14911) + 15088) - -1);
		a373 = 1;
		a357 = ((((((a357 * 1) % 38) - -4) * 5) % 38) + -17);
		a353 = a263;
		a276 = a253;
		a201 = (((((a201 % 94) - -135) + -37) * 10) / 9);
		a313 = 36;
		a320 = 13;
		a224 = 34;
		a368 = 1;
		a286 = a294[0];
		a173 = 36;
		a398 = 12;
		a75 = 32;
		a336 = 1;
		a296 = a384;
		a260 = 1;
		a300 = 0;
		a249 = ((((a249 % 15076) - 14923) - 2) - 0);
		a269 = 36;
		a228 = a264;
		a383 = a226[6];
		a234 = a372[5];
		a395 = 1;
		a307 = a227[4];
		a277 = ((((12 * 10) / 9) + 13194) - 13208);
		a184 = a157[(a211 + 5)];
		a370 = a311;
		a141 = a47[(a77 + -6)];
		a392 = a304;
		a338 = 3;
		a207 = 36;
		a270 = 12;
		a237 = 5;
		a218 = 33;
		a302 = a346[2];
		a382 = (((60 + 16003) + -35870) / 5);
		a243 = (((a243 - -10576) + 8625) + 10770);
		a206 = 10;
		a378 = 0;
		a230 = 7;
		a310 = (((((a310 + 7283) / 5) / 5) % 20) + 337);
		a211 = 7;
	}
	if ((((a207 == 33 && ((3 == a353[2]) && a16 == 1)) && a206 == 4) && ((a320 == 6 && (a132 != 1 && (a269 == 33 && ((a77 == 9 && (cf == 1 && input == inputs[6])) && a75 == 33)))) && a234 == a372[0]))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		cf = 0;
		a230 = 9;
		a276 = a253;
		a336 = 1;
		a224 = 35;
		a286 = a294[3];
		a260 = 1;
		a395 = 1;
		a339 = 1;
		a237 = 8;
		a240 = 1;
		a361 = 34;
		a357 = ((((a357 % 38) + -15) - 2) - 1);
		a398 = 10;
		a307 = a227[5];
		a256 = 34;
		a312 = 33;
		a383 = a226[0];
		a225 = a205[3];
		a320 = 9;
		a310 = (((((a310 * 1) + 14109) - -12457) % 14821) + 15178);
		a324 = a232[7];
		a313 = 36;
		a368 = 1;
		a129 = a92[(a77 + -8)];
		a270 = 15;
		a207 = 36;
		a249 = (((((a249 / 5) - -1686) / 5) % 71) + 426);
		a75 = 32;
		a333 = ((((a333 + 0) % 14976) + -47) - 14214);
		a173 = 34;
		a239 = a299;
		a338 = 10;
		a269 = 33;
		a302 = a346[3];
		a235 = a216[0];
		a370 = a318;
		a296 = a212;
		a201 = ((((a201 + 11667) % 14900) + -15098) + 0);
		a172 = (a359 - 2);
		a206 = 10;
		a386 = ((((a386 * 1) % 61) + 263) + -1);
		a218 = 36;
		a392 = a208;
		a353 = a399;
		a378 = 1;
		a243 = ((((a243 * 1) + 15996) % 14910) + -15088);
		a359 = 9;
	}
	if (((a320 == 6 && ((a270 == 10 && (3 == a353[2])) && a201 <= -199)) && (((a77 == 9 && (a339 == 1 && (a207 == 33 && ((a132 != 1 && cf == 1) && input == inputs[2])))) && a16 == 1) && a75 == 33))) {
		a164 += (a164 + 20) > a164 ? 3 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a184 = a157[((a270 * a320) - 57)];
		a134 = 0;
		a75 = 35;
		a295 = a366[a206];
	}
}
void calculate_outputm34(int input) {
	if (((a1 == a87[6] && ((a333 <= -47 && a313 == 33) && a359 == 3)) && (a235 == a216[0] && (a201 <= -199 && (a373 == 1 && (((a75 == 33 && (cf == 1 && input == inputs[4])) && a77 == 10) && a132 != 1)))))) {
		cf = 0;
		a228 = a292;
		a392 = a257;
		a230 = (a338 - 1);
		a353 = a399;
		a154 = ((a320 * a237) + -3);
		a57 = (a154 - 2);
		a359 = ((a77 - a77) + 5);
		a395 = 0;
		a201 = (((((((a201 * a310) % 14999) % 93) - 104) + -22040) * 1) + 22039);
		a370 = a285;
		a137 = a189;
		a260 = 0;
		a277 = (((((((a277 * a386) % 14999) % 78) + 70) / 5) + -15866) - -15901);
		a75 = 34;
		a218 = 34;
		a310 = (((((((a310 * a382) % 14999) % 77) + 238) / 5) - -28276) + -28041);
		a239 = a268;
		a269 = 34;
		a276 = a250;
		a333 = (((((((a333 * a357) % 14999) + -10066) % 14) + 163) + -26196) + 26195);
	}
}
void calculate_outputm36(int input) {
	if (((((a237 == 3 && (a361 == 33 && (a77 == 11 && (cf == 1 && a75 == 33)))) && input == inputs[4]) && (47 == a265[5])) && ((a99 == a26[7] && (a368 == 1 && (a256 == 33 && a132 != 1))) && (67 == a358[2])))) {
		a169 -= (a169 - 20) < a169 ? 2 : 0;
		cf = 0;
		a57 = ((a320 / a270) - -13);
		a218 = 34;
		a359 = ((a270 + a237) - 8);
		a353 = a399;
		a307 = a227[(a77 - 9)];
		a239 = a268;
		a310 = ((((((((a310 * a243) % 14999) % 77) - -238) + -1) / 5) * 51) / 10);
		a75 = 34;
		a240 = 1;
		a338 = (a230 + 2);
		a270 = (a338 + 6);
		a312 = 34;
		a228 = a292;
		a260 = 0;
		a276 = a250;
		a154 = ((a211 + a57) - -1);
		a137 = a189;
		a300 = 1;
		a395 = 0;
		a224 = 32;
		a370 = a285;
		a211 = a230;
		a368 = 1;
		a269 = 34;
		a230 = (a359 - 1);
	}
	if ((((a395 == 1 && (((a75 == 33 && cf == 1) && input == inputs[8]) && a99 == a26[7])) && a235 == a216[0]) && (((a300 == 1 && (a202 == a217[0] && (a307 == a227[0] && a132 != 1))) && a77 == 11) && a286 == a294[0]))) {
		cf = 0;
		if ((a300 != 1 || ((23 == a274[2]) && a184 == a157[0]))) {
			a239 = a268;
			a395 = 0;
			a353 = a399;
			a276 = a250;
			a307 = a227[((a230 * a338) + -7)];
			a370 = a285;
			a228 = a292;
			a230 = (a237 - -1);
			a260 = 0;
			a137 = a189;
			a224 = 32;
			a240 = 1;
			a154 = (a359 - -12);
			a211 = (a270 - 7);
			a300 = 1;
			a75 = 34;
			a218 = 34;
			a312 = 34;
			a57 = ((a338 - a359) - -13);
			a269 = 34;
			a368 = 1;
			a338 = ((a270 * a270) - 95);
			a310 = (((((((a310 * a382) % 14999) / 5) * 5) * 2) % 77) + 239);
			a359 = ((a270 - a320) + 1);
			a270 = a77;
		} else {
			a353 = a399;
			a398 = ((a338 + a359) - -6);
			a270 = ((a359 * a237) + 3);
			a143 = 34;
			a320 = ((a77 + a211) - 4);
			a224 = 32;
			a75 = 34;
			a234 = a372[((a359 * a237) + -7)];
			a260 = 1;
			a296 = a212;
			a339 = 1;
			a240 = 1;
			a230 = (a359 + 2);
			a265 = a376;
			a370 = a285;
			a201 = ((((((a382 * a382) % 14999) * 2) % 94) + 82) + 2);
			a307 = a227[((a359 * a270) + -34)];
			a395 = 0;
			a329 = 32;
			a373 = 0;
			a300 = 1;
			a358 = a335;
			a378 = 1;
			a173 = 33;
			a202 = a217[((a270 + a359) + -13)];
			a361 = 34;
			a57 = ((a359 + a359) + 5);
			a218 = 34;
			a310 = ((((((a310 * a357) % 14999) / 5) * 5) % 77) + 239);
		}
	}
}
void calculate_outputm2(int input) {
	if (((a260 == 1 && (a373 == 1 && a378 == 1)) && (a339 == 1 && (((cf == 1 && a77 == 8) && a270 == 10) && a211 == 1)))) {
		if (((a44 == 34 && cf == 1) && (a237 == 3 && ((((a260 == 1 && a313 == 33) && a211 == 1) && a225 == a205[0]) && (47 == a265[5]))))) {
			calculate_outputm29(input);
		}
	}
	if (((a338 == 3 && (a77 == 9 && cf == 1)) && ((((a207 == 33 && a333 <= -47) && a386 <= 77) && a383 == a226[0]) && (3 == a353[2])))) {
		if (((a218 == 33 && ((24 == a370[2]) && (37 == a392[3]))) && ((67 == a358[2]) && ((a260 == 1 && (cf == 1 && a16 == 1)) && a207 == 33)))) {
			calculate_outputm30(input);
		}
	}
	if ((((a359 == 3 && ((a77 == 10 && cf == 1) && a395 == 1)) && a218 == 33) && (a277 <= -10 && (a277 <= -10 && a234 == a372[0])))) {
		if (((a378 == 1 && (a1 == a87[6] && cf == 1)) && (a373 == 1 && ((a395 == 1 && (a218 == 33 && a225 == a205[0])) && (37 == a392[3]))))) {
			calculate_outputm34(input);
		}
	}
	if (((a243 <= -179 && (a320 == 6 && a211 == 1)) && (a224 == 33 && (a368 == 1 && ((a77 == 11 && cf == 1) && a359 == 3))))) {
		if (((a240 == 1 && (a307 == a227[0] && (a300 == 1 && ((a99 == a26[7] && cf == 1) && a378 == 1)))) && (a249 <= 152 && a312 == 33))) {
			calculate_outputm36(input);
		}
	}
}
void calculate_outputm40(int input) {
	if ((((a191 == a37[6] && (((a218 == 32 && (89 == a296[5])) && a173 == 33) && a75 == 32)) && a368 != 1) && (a286 == a294[1] && ((a230 == 4 && ((cf == 1 && input == inputs[8]) && a130 <= 134)) && a234 == a372[1])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if ((a1 == a87[5] || !(a338 == 9))) {
			a107 = 34;
			a173 = 34;
			a172 = ((a230 * a206) + -12);
		} else {
			a75 = 34;
			a57 = 17;
			a40 = a83;
			a25 = a68;
		}
	}
	if ((a270 == 11 && (input == inputs[0] && ((((-65 < a382) && (-39 >= a382)) && (((((((cf == 1 && a191 == a37[6]) && a130 <= 134) && a173 == 33) && a383 == a226[1]) && a307 == a227[1]) && a75 == 32) && ((-179 < a243) && (-156 >= a243)))) && ((77 < a386) && (201 >= a386)))))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a141 = a47[(a230 + -1)];
		a173 = 36;
		a184 = a157[2];
	}
	if (((((-10 < a277) && (148 >= a277)) && ((28 == a370[0]) && (a234 == a372[1] && a191 == a37[6]))) && ((a237 == 4 && (a173 == 33 && (a75 == 32 && ((a130 <= 134 && (cf == 1 && input == inputs[1])) && a302 == a346[1])))) && ((-65 < a382) && (-39 >= a382))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a5 -= (a5 - 20) < a5 ? 3 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a221 = 1;
		a207 = 35;
		a353 = a263;
		a237 = 4;
		a276 = a253;
		a173 = 36;
		a211 = 5;
		a386 = ((((a386 % 61) + 85) - 2) - -6);
		a256 = 36;
		a333 = ((((84 / 5) - 5769) * 10) / -9);
		a329 = 34;
		a373 = 1;
		a141 = a47[((a359 / a270) + 4)];
	}
	if (((((77 < a386) && (201 >= a386)) && (a359 == 4 && (a240 != 1 && a312 == 32))) && (a286 == a294[1] && (a75 == 32 && (a173 == 33 && (input == inputs[9] && (((a130 <= 134 && cf == 1) && a191 == a37[6]) && a235 == a216[1]))))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a67 += (a67 + 20) > a67 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a397 = (a230 - -7);
		a173 = 32;
		a125 = a30[((a397 / a397) + 2)];
	}
	if (((a235 == a216[1] && (((input == inputs[6] && (a191 == a37[6] && (cf == 1 && a173 == 33))) && a260 != 1) && a207 == 32)) && ((((((77 < a386) && (201 >= a386)) && a130 <= 134) && a75 == 32) && a218 == 32) && ((77 < a386) && (201 >= a386))))) {
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a75 = 34;
		a141 = a47[(a211 - 2)];
		a57 = ((a320 - a230) + 14);
		a40 = a65;
	}
	if (((a359 == 4 && ((a218 == 32 && a339 != 1) && a338 == 4)) && ((a270 == 11 && (a191 == a37[6] && (a75 == 32 && ((a130 <= 134 && (input == inputs[2] && cf == 1)) && a173 == 33)))) && (40 == a239[3])))) {
		a164 += (a164 + 20) > a164 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a173 = 34;
		a228 = a292;
		a225 = a205[2];
		a329 = 36;
		a358 = a335;
		a172 = ((a211 - a237) + 9);
		a353 = a241;
		a307 = a227[1];
		a99 = a26[(a206 - 3)];
	}
	if (((((a307 == a227[1] && ((a173 == 33 && cf == 1) && input == inputs[7])) && a235 == a216[1]) && (50 == a228[0])) && (((a75 == 32 && ((a324 == a232[1] && ((-10 < a277) && (148 >= a277))) && a130 <= 134)) && a225 == a205[1]) && a191 == a37[6]))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		a132 = 0;
		a75 = 33;
		a77 = ((a270 + a359) + -3);
		a129 = a92[(a77 - 9)];
	}
	if ((((a218 == 32 && (a269 == 32 && a173 == 33)) && a395 != 1) && (a312 == 32 && (((76 == a358[5]) && (((-65 < a382) && (-39 >= a382)) && (a75 == 32 && ((cf == 1 && a130 <= 134) && a191 == a37[6])))) && input == inputs[3])))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a169 -= (a169 - 20) < a169 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a66 = 0;
		a130 = ((((a130 / 5) + -12683) % 70) - -239);
	}
	if ((((a378 != 1 && ((a130 <= 134 && (a320 == 7 && a338 == 4)) && ((-188 < a357) && (-57 >= a357)))) && input == inputs[5]) && (((a173 == 33 && ((a191 == a37[6] && cf == 1) && a75 == 32)) && (89 == a296[5])) && a211 == 2))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a31 -= (a31 - 20) < a31 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a224 = 32;
		a218 = 35;
		a370 = a285;
		a155 = 35;
		a228 = a292;
		a302 = a346[4];
		a243 = (((((a243 % 11) - 159) + -4) + -16589) + 16595);
		a75 = 33;
		a132 = 0;
		a368 = 0;
		a260 = 0;
		a310 = (((((a310 * 5) + -28155) + -936) * -1) / 10);
		a269 = 35;
		a240 = 0;
		a358 = a335;
		a239 = a268;
		a211 = 8;
		a339 = 0;
		a230 = 9;
		a77 = (a270 - 4);
	}
	if (((((((a270 == 11 && a191 == a37[6]) && a75 == 32) && a339 != 1) && a237 == 4) && a286 == a294[1]) && (((-65 < a382) && (-39 >= a382)) && ((a130 <= 134 && (a173 == 33 && (cf == 1 && input == inputs[4]))) && a368 != 1)))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a98 -= (a98 - 20) < a98 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		a336 = 1;
		a99 = a26[((a206 * a359) + -19)];
		a277 = (((a277 - -3539) - -5461) - -14502);
		a228 = a292;
		a373 = 1;
		a329 = 36;
		a383 = a226[3];
		a234 = a372[6];
		a173 = 34;
		a239 = a242;
		a211 = 3;
		a353 = a399;
		a324 = a232[3];
		a358 = a351;
		a276 = a253;
		a172 = ((a359 - a206) - -8);
	}
}
void calculate_outputm44(int input) {
	if (((((a359 == 4 && ((a173 == 33 && cf == 1) && ((203 < a13) && (325 >= a13)))) && ((77 < a386) && (201 >= a386))) && a230 == 4) && (a235 == a216[1] && ((input == inputs[1] && ((a75 == 32 && a398 == 11) && 493 < a130)) && a235 == a216[1])))) {
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a31 += (a31 + 20) > a31 ? 3 : 0;
		cf = 0;
		a134 = 0;
		a75 = 35;
		a196 = ((a270 / a206) + 9);
		a295 = a366[((a196 / a196) - 1)];
	}
	if (((a173 == 33 && (a269 == 32 && ((493 < a130 && (a75 == 32 && ((((203 < a13) && (325 >= a13)) && cf == 1) && input == inputs[2]))) && a260 != 1))) && (a312 == 32 && (a237 == 4 && (a339 != 1 && a378 != 1))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a53 = ((((((a130 * a130) % 14999) / 5) / 5) % 59) - -14);
		a75 = 35;
		a134 = 0;
		a392 = a257;
		a211 = 8;
		a234 = a372[1];
		a359 = 4;
		a361 = 34;
		a202 = a217[1];
		a358 = a351;
		a398 = 13;
		a339 = 0;
		a218 = 32;
		a269 = 36;
		a276 = a289;
		a373 = 0;
		a224 = 32;
		a228 = a264;
		a296 = a384;
		a239 = a299;
		a295 = a366[5];
	}
	if (((((((-179 < a243) && (-156 >= a243)) && (((40 == a239[3]) && (a313 == 32 && ((77 < a386) && (201 >= a386)))) && ((203 < a13) && (325 >= a13)))) && a207 == 32) && a173 == 33) && (a398 == 11 && (((cf == 1 && input == inputs[9]) && a75 == 32) && 493 < a130)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if (((60 == a3[3]) || (a171 == 34 || (a184 == a157[4] && (a136 == 7 || a141 == a47[2]))))) {
			a358 = a351;
			a302 = a346[3];
			a386 = ((((a386 - 15631) * 10) / 9) - 12574);
			a329 = 33;
			a269 = 36;
			a286 = a294[4];
			a339 = 1;
			a353 = a241;
			a249 = ((((a249 * -5) * 5) + 6916) + -17975);
			a296 = a362;
			a240 = 0;
			a218 = 35;
			a382 = ((((75 - 116) - 26037) / 5) + 5156);
			a276 = a253;
			a338 = 6;
			a373 = 1;
			a333 = ((((92 - -3238) / 5) - -2348) + -2854);
			a211 = 6;
			a243 = (((a243 + -4607) * 5) * 1);
			a313 = 35;
			a207 = 32;
			a336 = 1;
			a57 = ((a230 - a230) + 10);
			a398 = 16;
			a359 = 7;
			a270 = 10;
			a368 = 1;
			a324 = a232[5];
			a312 = 34;
			a310 = ((((a310 + 23056) - 37547) * 10) / -9);
			a307 = a227[5];
			a202 = a217[4];
			a277 = (((a277 - -15514) + 1898) * 1);
			a320 = 9;
			a75 = 34;
			a265 = a293;
			a201 = (((((73 * 10) / 9) / 5) + -29551) + 29524);
			a300 = 0;
			a224 = 35;
			a392 = a208;
			a260 = 0;
			a239 = a299;
			a230 = 9;
			a370 = a318;
			a357 = (((((a357 % 65) + -63) * 1) * 10) / 9);
			a234 = a372[1];
			a228 = a264;
			a235 = a216[2];
			a237 = 10;
			a378 = 1;
			a361 = 34;
			a155 = 36;
			a206 = 8;
			a158 = (a57 - -1);
		} else {
			a256 = 33;
			a234 = a372[0];
			a395 = 1;
			a172 = ((a359 - a359) - -1);
			a225 = a205[5];
			a336 = 1;
			a173 = 34;
			a277 = (((a277 / 5) - -29824) + -29794);
			a333 = ((((76 + -24159) * -1) / 10) - -1271);
			a320 = 10;
			a228 = a264;
			a353 = a263;
			a129 = a92[(a206 - 3)];
		}
	}
	if ((((a378 != 1 && (input == inputs[4] && ((a300 != 1 && a361 == 32) && a235 == a216[1]))) && a398 == 11) && (((11 == a353[4]) && (a173 == 33 && ((cf == 1 && ((203 < a13) && (325 >= a13))) && a75 == 32))) && 493 < a130))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a162 += (a162 + 20) > a162 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		cf = 0;
		if ((a278 == 5 || ((((233 < a17) && (414 >= a17)) || a71 == a175[6]) && !(31 == a137[0])))) {
			a81 = a167[(a338 + -4)];
			a57 = (a206 - -7);
			a75 = 34;
			a99 = a26[(a57 + -11)];
		} else {
			a132 = 0;
			a75 = 33;
			a77 = (a270 - 6);
			a136 = ((a211 * a211) - -8);
		}
	}
	if (((((((103 == a276[1]) && input == inputs[6]) && 493 < a130) && ((-188 < a357) && (-57 >= a357))) && a206 == 5) && ((((((((203 < a13) && (325 >= a13)) && cf == 1) && a173 == 33) && a202 == a217[1]) && a378 != 1) && a75 == 32) && a202 == a217[1]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a174 -= (a174 - 20) < a174 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a35 += (a35 + 20) > a35 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a91 = ((a230 + a359) + 3);
		a336 = 1;
		a243 = (((((a243 * 10) / 8) * 5) - -6523) - 10112);
		a329 = 36;
		a395 = 1;
		a296 = a212;
		a207 = 32;
		a383 = a226[0];
		a333 = ((((16 * 10) / -3) + -7855) + -12401);
		a235 = a216[0];
		a320 = 6;
		a312 = 35;
		a338 = 4;
		a286 = a294[6];
		a173 = 35;
		a1 = a87[(a206 + 1)];
	}
	if (((a313 == 32 && (((((-188 < a357) && (-57 >= a357)) && (a300 != 1 && a361 == 32)) && a398 == 11) && a75 == 32)) && (((203 < a13) && (325 >= a13)) && ((a373 != 1 && (493 < a130 && (cf == 1 && input == inputs[3]))) && a173 == 33)))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a174 += (a174 + 20) > a174 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if ((59 == a228[3])) {
			a218 = 36;
			a276 = a250;
			a339 = 0;
			a134 = 0;
			a359 = 4;
			a228 = a292;
			a358 = a351;
			a234 = a372[6];
			a75 = 35;
			a392 = a304;
			a202 = a217[1];
			a296 = a384;
			a269 = 36;
			a211 = 4;
			a239 = a268;
			a224 = 35;
			a398 = 14;
			a373 = 0;
			a361 = 32;
			a295 = a366[(a338 + 1)];
			a53 = ((((((a310 * a13) % 14999) % 59) - 44) / 5) / 5);
		} else {
			a237 = 7;
			a105 = 34;
			a382 = (((90 - -11265) + -38923) * 1);
			a312 = 36;
			a276 = a289;
			a361 = 36;
			a302 = a346[5];
			a57 = 10;
			a239 = a268;
			a75 = 34;
			a386 = ((((a386 * 5) % 61) + 258) + 4);
			a202 = a217[1];
			a240 = 0;
			a270 = 11;
			a296 = a384;
			a398 = 15;
			a353 = a263;
			a329 = 33;
			a218 = 36;
			a320 = 13;
			a230 = 10;
			a235 = a216[2];
			a211 = 8;
			a201 = (((((64 * 28) / 10) * 5) * 10) / 9);
			a357 = ((((a357 - 13003) + 149) * 10) / 9);
			a358 = a351;
			a207 = 32;
			a307 = a227[3];
			a378 = 0;
			a392 = a304;
			a269 = 34;
			a206 = 7;
			a368 = 0;
			a228 = a292;
			a310 = ((((a310 - -17283) + 4067) % 77) + 231);
			a359 = 4;
			a373 = 0;
			a339 = 1;
			a370 = a311;
			a277 = ((((a277 - -4988) + -20341) % 78) + 79);
			a324 = a232[3];
			a313 = 33;
			a336 = 0;
			a260 = 0;
			a338 = 4;
			a243 = (((a243 / 5) * 5) + 44);
			a158 = (a57 + -4);
		}
	}
	if (((((((203 < a13) && (325 >= a13)) && (a373 != 1 && 493 < a130)) && (28 == a370[0])) && a329 == 32) && ((89 == a296[5]) && ((a329 == 32 && (input == inputs[5] && ((a75 == 32 && cf == 1) && a173 == 33))) && ((160 < a310) && (316 >= a310)))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a162 -= (a162 - 20) < a162 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		if ((!(a154 == 12) || ((201 < a386) && (325 >= a386)))) {
			a81 = a167[((a338 + a359) + -6)];
			a224 = 33;
			a234 = a372[6];
			a202 = a217[7];
			a158 = a270;
			a201 = (((((36 * 10) / -1) * 5) + 3003) - 15794);
			a378 = 0;
			a357 = ((((a357 % 65) - 93) + -7) + -21);
			a359 = 7;
			a240 = 0;
			a243 = (((((a243 + 9948) * 10) / 9) * 10) / 9);
			a333 = ((((65 + 8843) * 10) / 9) + 8996);
			a336 = 0;
			a307 = a227[4];
			a286 = a294[6];
			a228 = a229;
			a302 = a346[1];
			a270 = 14;
			a249 = ((((((a249 * 5) % 101) - -243) / 5) * 39) / 10);
			a239 = a242;
			a398 = 10;
			a276 = a289;
			a225 = a205[7];
			a296 = a384;
			a57 = (a158 + 1);
			a312 = 35;
			a218 = 35;
			a329 = 32;
			a320 = 13;
			a324 = a232[7];
			a277 = ((((a277 - -5007) * 10) / 9) * 5);
			a339 = 1;
			a230 = 10;
			a386 = (((a386 / 5) - 7064) * 4);
			a310 = ((((a310 * 5) * 5) / 5) * -5);
			a368 = 0;
			a75 = 34;
			a237 = 7;
			a269 = 36;
			a235 = a216[1];
			a392 = a208;
			a382 = (((((91 + 23090) * -1) / 10) + 14454) - 27585);
			a300 = 0;
			a353 = a263;
			a211 = 7;
			a207 = 35;
			a370 = a318;
			a373 = 1;
			a206 = 9;
			a265 = a293;
			a338 = 3;
		} else {
			a210 = 1;
			a75 = 34;
			a143 = 35;
			a57 = 11;
		}
	}
	if ((((103 == a276[1]) && (((152 < a249) && (355 >= a249)) && (((203 < a13) && (325 >= a13)) && (a173 == 33 && a269 == 32)))) && ((a307 == a227[1] && ((((-188 < a357) && (-57 >= a357)) && ((cf == 1 && input == inputs[7]) && a75 == 32)) && 493 < a130)) && a207 == 32))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		if (((!(a184 == a157[7]) || ((-156 < a243) && (-68 >= a243))) && !(a200 == 8))) {
			a81 = a167[(a270 + -11)];
			a173 = 32;
			a125 = a30[(a338 + 1)];
		} else {
			a173 = 35;
			a91 = (a237 - -9);
			a195 = a58;
		}
	}
	if (((493 < a130 && a300 != 1) && ((((53 == a265[5]) && (input == inputs[0] && (((a75 == 32 && (((203 < a13) && (325 >= a13)) && (a173 == 33 && cf == 1))) && (76 == a358[5])) && a207 == 32))) && a286 == a294[1]) && a286 == a294[1]))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		if (a368 == 1) {
			a57 = (a359 - -11);
			a141 = a47[((a57 - a270) + -4)];
			a75 = 34;
			a72 = (((((a130 * a13) % 14999) + -25309) - 2308) - 1175);
		} else {
			a224 = 35;
			a320 = 11;
			a230 = 7;
			a368 = 0;
			a395 = 0;
			a239 = a299;
			a240 = 0;
			a300 = 0;
			a234 = a372[7];
			a329 = 36;
			a339 = 0;
			a206 = 7;
			a302 = a346[7];
			a361 = 35;
			a296 = a362;
			a228 = a292;
			a358 = a335;
			a265 = a293;
			a357 = ((((a357 * -4) / 10) - -15960) + 8701);
			a338 = 5;
			a276 = a253;
			a256 = 36;
			a359 = 6;
			a75 = 36;
			a386 = (((a386 + 2558) + 11847) / 5);
			a218 = 34;
			a243 = (((a243 * -5) + 28522) + 392);
			a202 = a217[7];
			a324 = a232[5];
			a260 = 0;
			a312 = 35;
			a249 = (((a249 * -5) - -6105) + -16926);
			a235 = a216[3];
			a270 = 15;
			a378 = 0;
			a277 = (((a277 + 28572) - 27728) + 20150);
			a286 = a294[4];
			a225 = a205[3];
			a398 = 13;
			a353 = a241;
			a146 = 0;
			a16 = 1;
			a373 = 0;
			a237 = 6;
			a383 = a226[4];
			a207 = 35;
			a73 = (((((((a130 * a13) % 14999) % 54) + 214) * 5) % 54) + 172);
		}
	}
	if ((((a173 == 33 && (a368 != 1 && (a359 == 4 && a324 == a232[1]))) && ((203 < a13) && (325 >= a13))) && ((((11 == a353[4]) && (a75 == 32 && ((input == inputs[8] && cf == 1) && 493 < a130))) && a378 != 1) && ((160 < a310) && (316 >= a310))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a5 -= (a5 - 20) < a5 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a278 = a326[7];
		a75 = 34;
		a57 = (a206 - -11);
		a81 = a167[((a57 / a57) - -4)];
	}
}
void calculate_outputm3(int input) {
	if (((((a224 == 32 && ((43 == a392[3]) && a206 == 5)) && a225 == a205[1]) && a206 == 5) && ((40 == a239[3]) && (cf == 1 && a130 <= 134)))) {
		if (((a320 == 7 && (a235 == a216[1] && a368 != 1)) && (a368 != 1 && ((a286 == a294[1] && (a191 == a37[6] && cf == 1)) && a302 == a346[1])))) {
			calculate_outputm40(input);
		}
	}
	if (((a224 == 32 && ((493 < a130 && cf == 1) && a270 == 11)) && (a224 == 32 && (a378 != 1 && ((40 == a239[3]) && a218 == 32))))) {
		if (((((-188 < a357) && (-57 >= a357)) && (cf == 1 && ((203 < a13) && (325 >= a13)))) && (a234 == a372[1] && ((11 == a353[4]) && ((a235 == a216[1] && ((152 < a249) && (355 >= a249))) && (11 == a353[4])))))) {
			calculate_outputm44(input);
		}
	}
}
void calculate_outputm46(int input) {
	if (((((a240 != 1 && ((a302 == a346[1] && (a173 == 32 && (402 < a54 && ((a125 == a30[0] && cf == 1) && input == inputs[7])))) && ((160 < a310) && (316 >= a310)))) && ((160 < a310) && (316 >= a310))) && ((a75 == 32 && a235 == a216[1]) && ((-188 < a357) && (-57 >= a357)))) && a12 == 5636)) {
		a120 -= (a120 - 20) < a120 ? 4 : 0;
		cf = 0;
		a125 = a30[5];
		a81 = a167[(a206 - 2)];
	}
	if (((((a339 != 1 && (a237 == 4 && ((a125 == a30[0] && (a338 == 4 && a338 == 4)) && a75 == 32))) && (76 == a358[5])) && (a270 == 11 && (((a173 == 32 && cf == 1) && 402 < a54) && input == inputs[6]))) && a67 >= -2)) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		cf = 0;
		a75 = 34;
		a201 = ((((((a201 * a386) % 14999) % 94) - -83) + 19492) + -19491);
		a382 = ((((((a382 * a201) * 2) % 107) + 68) - -6308) + -6306);
		a358 = a335;
		a224 = 34;
		a143 = 36;
		a357 = (((((((a357 * a243) % 14999) % 38) - 25) + -17) * 9) / 10);
		a240 = 1;
		a57 = 11;
		a202 = a217[((a237 * a270) - 42)];
		a368 = 1;
		a230 = (a398 + -6);
		a69 = 32;
		a378 = 1;
		a307 = a227[a211];
		a218 = 34;
		a265 = a376;
		a313 = 34;
		a333 = ((((((a333 * a201) / 5) / 5) / 5) % 14) - -163);
		a386 = (((((((a386 * a54) % 14999) / 5) % 61) + 252) - -10419) + -10466);
	}
	if ((((a286 == a294[1] && (a202 == a217[1] && (a173 == 32 && ((cf == 1 && 402 < a54) && input == inputs[2])))) && (a398 == 11 && (a378 != 1 && (a75 == 32 && ((a329 == 32 && ((-47 < a333) && (147 >= a333))) && a125 == a30[0]))))) && a169 >= 2)) {
		a164 += (a164 + 20) > a164 ? 1 : 0;
		cf = 0;
		a240 = 1;
		a211 = (a359 - 1);
		a218 = 34;
		a57 = (a320 + 10);
		a40 = a83;
		a382 = ((((((a382 * a201) % 107) - -7) * 10) / 9) + -21);
		a265 = a376;
		a378 = 1;
		a357 = ((((((a357 * a310) % 14999) + 27436) * 1) % 38) - 32);
		a358 = a335;
		a276 = a250;
		a202 = a217[(a398 + -9)];
		a75 = 34;
		a307 = a227[(a338 + -2)];
		a269 = 34;
		a320 = (a237 - -4);
		a239 = a268;
		a386 = ((((((a386 * a333) / 5) / 5) + 11356) % 61) - -256);
		a302 = a346[(a270 - 9)];
		a336 = 1;
		a333 = (((((((a333 * a277) % 14999) * 2) / 5) / 5) % 14) - -161);
		a25 = a76;
	}
	if (((a230 == 4 && (a206 == 5 && (a202 == a217[1] && ((402 < a54 && (cf == 1 && a173 == 32)) && a75 == 32)))) && ((a339 != 1 && (a300 != 1 && (input == inputs[4] && a329 == 32))) && a125 == a30[0]))) {
		a161 -= (a161 - 20) < a161 ? 4 : 0;
		cf = 0;
		a296 = a384;
		a249 = ((((((((a277 * a386) % 14999) + 1596) % 71) - -372) - 96) * 13) / 10);
		a81 = a167[(a237 + -2)];
		a206 = ((a270 - a270) - -6);
		a265 = a293;
		a339 = 1;
		a368 = 1;
		a243 = (((((((a249 * a201) % 14999) % 43) + -112) + 11002) + 15016) - 26018);
		a158 = ((a211 + a359) + 3);
		a386 = ((((((a277 * a249) % 14999) - -5707) * 1) % 61) + 81);
		a239 = a242;
		a378 = 1;
		a211 = ((a338 + a270) - 14);
		a218 = 34;
		a256 = 32;
		a240 = 1;
		a359 = (a206 - 3);
		a225 = a205[(a270 - 10)];
		a224 = 34;
		a358 = a335;
		a269 = 34;
		a370 = a311;
		a202 = a217[(a270 + -9)];
		a312 = 32;
		a276 = a253;
		a75 = 34;
		a313 = 32;
		a57 = (a158 + 3);
		a357 = (((((a357 * a243) % 38) - 25) - 16009) + 16002);
		a361 = 32;
		a333 = ((((((a333 * a382) * 3) % 14) - -161) + -4505) + 4507);
		a392 = a304;
		a382 = ((((((a333 * a243) % 12) - 51) / 5) * 49) / 10);
		a329 = 32;
		a373 = 0;
		a235 = a216[(a338 + -2)];
		a207 = 33;
		a398 = (a338 - -8);
		a320 = a206;
		a234 = a372[(a206 - 4)];
		a302 = a346[((a270 - a206) + -3)];
		a336 = 1;
		a310 = ((((((a310 * a201) % 14999) % 20) + 336) * 1) + 0);
		a230 = ((a270 / a206) - -4);
		a260 = 0;
		a300 = 0;
		a237 = (a338 + 1);
		a201 = ((((((a243 * a333) / 5) % 93) + -72) * 10) / 9);
		a395 = 0;
		a307 = a227[(a338 - 2)];
		a324 = a232[(a270 + -11)];
		a286 = a294[(a57 + -11)];
		a338 = ((a270 / a398) - -3);
		a270 = (a158 - -2);
	}
	if (((a378 != 1 && (((77 < a386) && (201 >= a386)) && ((a313 == 32 && a125 == a30[0]) && a173 == 32))) && ((76 == a358[5]) && (((((cf == 1 && input == inputs[8]) && a75 == 32) && a336 != 1) && 402 < a54) && ((-65 < a382) && (-39 >= a382)))))) {
		a122 -= (a122 - 20) < a122 ? 4 : 0;
		cf = 0;
		a358 = a348;
		a353 = a263;
		a239 = a242;
		a155 = 35;
		a329 = 33;
		a368 = 1;
		a77 = (a206 - -2);
		a211 = ((a338 / a398) - -1);
		a339 = 1;
		a75 = 33;
		a370 = a318;
		a310 = (((((((a310 * a54) % 14999) + -19667) * 10) / 9) * 10) / 9);
		a230 = ((a270 + a270) + -19);
		a269 = 33;
		a240 = 1;
		a276 = a253;
		a373 = 1;
		a260 = 1;
		a132 = 0;
		a243 = (((((a243 * a357) % 14999) / 5) + -14274) + -1066);
		a218 = 33;
		a302 = a346[(a237 - 4)];
	}
	if (((((160 < a310) && (316 >= a310)) && (402 < a54 && (a373 != 1 && ((a75 == 32 && cf == 1) && a125 == a30[0])))) && ((((a235 == a216[1] && (a368 != 1 && (103 == a276[1]))) && a338 == 4) && a173 == 32) && input == inputs[9]))) {
		a5 -= (a5 - 20) < a5 ? 4 : 0;
		cf = 0;
		if ((a129 == a92[0] || a278 == a326[1])) {
			a173 = 36;
			a359 = ((a230 + a230) - 5);
			a224 = 32;
			a141 = a47[(a237 - 3)];
			a237 = ((a230 - a230) + 3);
			a373 = 1;
			a353 = a263;
			a333 = ((((((a333 * a54) % 14999) % 14976) - 15022) + -3) * 1);
			a228 = a229;
			a383 = a226[((a398 - a206) - 6)];
			a398 = (a338 - -6);
			a218 = 33;
			a225 = a205[(a211 - 2)];
			a300 = 1;
			a277 = (((((((a201 * a386) % 14999) - -24997) % 78) - 1) + 21879) + -21844);
			a239 = a242;
			a211 = (a338 - 3);
			a234 = a372[((a320 - a338) - 3)];
			a312 = 33;
			a42 = (a338 - -4);
			a338 = (a270 - 8);
			a230 = 3;
		} else {
			a207 = 33;
			a353 = a263;
			a368 = 1;
			a386 = ((((((a333 * a357) % 15038) - 14960) - -511) + 24773) + -25286);
			a230 = ((a270 * a206) - 52);
			a224 = 32;
			a277 = ((((((a333 * a382) - 16543) + 17340) * 3) % 14995) - 15004);
			a196 = ((a270 - a270) + 10);
			a339 = 1;
			a129 = a92[((a270 - a270) - -2)];
			a249 = (((((a310 * a386) % 14999) - 14992) * 1) * 1);
			a134 = 1;
			a313 = 33;
			a276 = a253;
			a269 = 33;
			a373 = 1;
			a240 = 1;
			a312 = 33;
			a237 = (a320 + -4);
			a359 = ((a230 + a230) - 3);
			a320 = (a359 - -3);
			a75 = 35;
			a206 = (a237 - -1);
			a333 = (((((((a333 * a249) % 14999) % 14976) + -15022) - 2) / 5) - 11856);
			a260 = 1;
			a338 = (a398 - 8);
			a270 = (a359 + 7);
			a398 = ((a211 / a359) - -10);
		}
	}
	if ((((a218 == 32 && (((a173 == 32 && (input == inputs[3] && a300 != 1)) && a260 != 1) && (40 == a239[3]))) && (402 < a54 && ((a398 == 11 && ((a75 == 32 && cf == 1) && a125 == a30[0])) && ((152 < a249) && (355 >= a249))))) && a133 == 2186)) {
		a67 += (a67 + 20) > a67 ? 1 : 0;
		cf = 0;
		a134 = 1;
		a75 = 35;
		a54 = (((((a54 * a243) % 14999) + -10519) + -2630) - 1155);
		a196 = ((a359 / a270) - -12);
	}
	if ((((a395 != 1 && (a313 == 32 && (a125 == a30[0] && ((((402 < a54 && cf == 1) && input == inputs[0]) && (43 == a392[3])) && a307 == a227[1])))) && ((89 == a296[5]) && (a75 == 32 && (a173 == 32 && a270 == 11)))) && a50 == 82)) {
		a5 -= (a5 - 20) < a5 ? 2 : 0;
		cf = 0;
		a107 = 34;
		a173 = 34;
		a172 = 8;
	}
	if ((((((-179 < a243) && (-156 >= a243)) && (((-47 < a333) && (147 >= a333)) && ((53 == a265[5]) && a302 == a346[1]))) && ((((a329 == 32 && (a235 == a216[1] && ((cf == 1 && input == inputs[1]) && a75 == 32))) && a125 == a30[0]) && a173 == 32) && 402 < a54)) && a35 == 3324)) {
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		cf = 0;
		a75 = 34;
		a57 = ((a230 + a398) - -2);
		a141 = a47[((a320 / a237) + -1)];
		a40 = a65;
	}
	if ((((((a173 == 32 && a202 == a217[1]) && a75 == 32) && ((-179 < a243) && (-156 >= a243))) && a237 == 4) && (a395 != 1 && (a256 == 32 && ((28 == a370[0]) && (input == inputs[5] && (a125 == a30[0] && (402 < a54 && cf == 1)))))))) {
		a122 += (a122 + 20) > a122 ? 2 : 0;
		a63 += (a63 + 20) > a63 ? 1 : 0;
		a51 -= (a51 - 20) < a51 ? 4 : 0;
		a161 += (a161 + 20) > a161 ? 2 : 0;
		a168 -= (a168 - 20) < a168 ? 4 : 0;
		cf = 0;
		a172 = ((a338 - a320) + 4);
		a225 = a205[(a359 + -3)];
		a224 = 32;
		a173 = 34;
		a383 = a226[(a172 + 1)];
		a129 = a92[(a172 - -1)];
	}
}
void calculate_outputm47(int input) {
	if ((((a8 == 10 && (a173 == 32 && ((103 == a276[1]) && ((77 < a386) && (201 >= a386))))) && (11 == a353[4])) && (((89 == a296[5]) && (((77 < a386) && (201 >= a386)) && ((a125 == a30[1] && (cf == 1 && input == inputs[8])) && a361 == 32))) && a75 == 32))) {
		a174 -= (a174 - 20) < a174 ? 2 : 0;
		a67 += (a67 + 20) > a67 ? 1 : 0;
		cf = 0;
		a353 = a399;
		a357 = (((((((a249 * a201) % 14999) + 724) % 38) - 18) + 11850) + -11850);
		a359 = (a8 + -5);
		a320 = ((a359 * a8) + -42);
		a310 = (((((((a357 * a201) % 20) - -336) * 5) - 6114) % 20) + 337);
		a370 = a311;
		a333 = ((((((a243 * a310) % 14999) + 9569) / 5) % 14) + 161);
		a373 = 0;
		a75 = 34;
		a230 = (a320 - 3);
		a228 = a229;
		a296 = a362;
		a312 = 34;
		a211 = (a8 + -7);
		a206 = (a8 + -4);
		a249 = ((((((a357 * a357) % 71) - -426) * 1) - -12240) + -12237);
		a278 = a326[((a398 + a338) - 12)];
		a277 = (((((a277 * a386) % 95) + 244) + -22886) + 22885);
		a184 = a157[((a270 * a270) + -119)];
		a57 = ((a237 * a8) - 24);
		a237 = ((a359 - a359) - -5);
		a234 = a372[(a359 - 3)];
		a382 = ((((((a382 * a243) % 107) + 69) * 5) % 107) - -58);
		a336 = 1;
		a240 = 1;
		a276 = a250;
		a302 = a346[(a206 + -4)];
		a270 = ((a8 * a338) + -28);
		a307 = a227[(a8 + -8)];
		a338 = ((a359 - a8) - -10);
		a386 = (((((((a357 * a357) - -13936) % 61) + 235) * 5) % 61) + 253);
		a260 = 1;
		a207 = 33;
		a339 = 0;
		a224 = 34;
		a368 = 1;
		a398 = (a359 + 7);
		a202 = a217[(a359 - 4)];
		a361 = 34;
		a358 = a335;
		a269 = 34;
		a243 = (((((a357 * a357) * 5) + 8100) % 43) + -147);
		a378 = 1;
		a225 = a205[(a211 - 1)];
	}
	if ((((a240 != 1 && (a260 != 1 && a339 != 1)) && (((a302 == a346[1] && (a125 == a30[1] && ((a173 == 32 && (input == inputs[0] && (cf == 1 && a75 == 32))) && ((152 < a249) && (355 >= a249))))) && a378 != 1) && a8 == 10)) && a164 <= 3)) {
		a168 += (a168 + 20) > a168 ? 3 : 0;
		cf = 0;
		a173 = 33;
		a130 = (((((a201 * a277) % 15067) + -14932) - 2) - 0);
		a239 = a299;
		a191 = a37[(a8 - 5)];
	}
	if ((((a75 == 32 && (((a270 == 11 && (28 == a370[0])) && a235 == a216[1]) && input == inputs[1])) && (103 == a276[1])) && ((a324 == a232[1] && (((-65 < a382) && (-39 >= a382)) && (a8 == 10 && (cf == 1 && a125 == a30[1])))) && a173 == 32))) {
		cf = 0;
		a265 = a293;
		a353 = a399;
		a225 = a205[(a270 - 11)];
		a286 = a294[(a320 / a237)];
		a125 = a30[(a8 - 10)];
		a277 = (((((a277 * a201) % 95) + 244) + 22070) - 22069);
		a202 = a217[((a270 - a270) - -1)];
		a218 = 32;
		a207 = 32;
		a54 = (((7 / 5) - -15826) + 1120);
		a256 = 32;
		a333 = ((((((a243 * a201) % 14999) % 96) - 30) - 4) + 44);
		a336 = 0;
		a239 = a299;
		a228 = a229;
		a211 = (a359 - 2);
		a300 = 0;
		a224 = 33;
		a395 = 0;
		a329 = 32;
		a361 = 32;
		a383 = a226[((a237 + a206) + -9)];
		a234 = a372[(a230 / a211)];
	}
	if (((((((-199 < a201) && (-12 >= a201)) && (((a75 == 32 && (a378 != 1 && a307 == a227[1])) && (50 == a228[0])) && a237 == 4)) && a373 != 1) && (((a173 == 32 && (cf == 1 && input == inputs[3])) && a125 == a30[1]) && a8 == 10)) && a120 >= 3)) {
		cf = 0;
		a75 = 34;
		a277 = (((((((a277 * a249) % 14999) % 95) + 244) / 5) + -16846) + 16993);
		a158 = (a270 - 6);
		a240 = 1;
		a353 = a399;
		a200 = a115[(a206 - -1)];
		a392 = a304;
		a243 = ((((((((a310 * a277) % 14999) % 43) - 120) + 3) / 5) * 59) / 10);
		a307 = a227[(a398 - 9)];
		a339 = 0;
		a320 = (a237 + 4);
		a324 = a232[(a8 - 8)];
		a225 = a205[(a206 + -3)];
		a57 = ((a8 - a8) - -10);
		a338 = (a230 + 1);
		a357 = (((((((a357 * a243) + 830) % 38) + -32) * 5) % 38) + -18);
	}
	if (((((a8 == 10 && a302 == a346[1]) && ((-179 < a243) && (-156 >= a243))) && (a368 != 1 && (((160 < a310) && (316 >= a310)) && ((a173 == 32 && ((input == inputs[4] && (a125 == a30[1] && (cf == 1 && a75 == 32))) && a224 == 32)) && a313 == 32)))) && (a131 % 2 == 0))) {
		a164 += (a164 + 20) > a164 ? 2 : 0;
		cf = 0;
		a75 = 34;
		a134 = 1;
		a57 = (a270 - -5);
		a278 = a326[((a57 + a8) - 20)];
	}
	if ((((input == inputs[7] && ((76 == a358[5]) && ((77 < a386) && (201 >= a386)))) && (((-199 < a201) && (-12 >= a201)) && ((a324 == a232[1] && (((a225 == a205[1] && ((a75 == 32 && cf == 1) && a8 == 10)) && a173 == 32) && a260 != 1)) && a125 == a30[1]))) && a122 >= 3)) {
		cf = 0;
		a269 = 33;
		a296 = a212;
		a295 = a366[(a320 + -2)];
		a134 = 0;
		a359 = (a237 - 1);
		a218 = 33;
		a339 = 1;
		a75 = 35;
		a361 = 33;
		a398 = ((a206 * a206) + -15);
		a276 = a253;
		a373 = 1;
		a224 = 33;
		a239 = a242;
		a228 = a229;
		a320 = ((a359 / a230) + 6);
		a358 = a348;
		a392 = a208;
		a53 = ((((37 + 27184) / 5) - -14483) + -19925);
	}
}
void calculate_outputm48(int input) {
	if (((a211 == 2 && (a202 == a217[1] && a339 != 1)) && ((40 == a239[3]) && (a324 == a232[1] && (a240 != 1 && (input == inputs[6] && ((a125 == a30[1] && (a75 == 32 && (cf == 1 && a173 == 32))) && a8 == 11))))))) {
		a178 += (a178 + 20) > a178 ? 1 : 0;
		cf = 0;
		a230 = (a8 - 6);
		a265 = a376;
		a368 = 1;
		a357 = ((((((a243 * a382) + 16910) * 1) / 5) % 38) + -29);
		a202 = a217[(a230 + -3)];
		a339 = 1;
		a361 = 34;
		a57 = (a206 + 6);
		a320 = (a230 + 3);
		a260 = 1;
		a353 = a399;
		a225 = a205[(a206 - 5)];
		a398 = (a237 - -8);
		a234 = a372[(a338 + -2)];
		a338 = (a237 + -1);
		a324 = a232[(a359 - 2)];
		a359 = ((a230 + a237) + -6);
		a211 = ((a230 + a320) - 12);
		a358 = a335;
		a201 = ((((((a201 * a357) * 2) % 94) + 84) + 12128) - 12128);
		a312 = 33;
		a296 = a212;
		a75 = 34;
		a270 = a398;
		a276 = a253;
		a228 = a229;
		a173 = 33;
		a382 = ((((((a382 * a333) * 2) * 1) + -1106) % 107) - -155);
		a240 = 1;
		a313 = 33;
		a329 = 32;
		a206 = a237;
		a143 = 34;
		a373 = 0;
		a237 = (a230 + -2);
	}
	if ((((a383 == a226[1] && (a286 == a294[1] && (a8 == 11 && a225 == a205[1]))) && (89 == a296[5])) && (a240 != 1 && ((((a125 == a30[1] && (a75 == 32 && cf == 1)) && a313 == 32) && input == inputs[0]) && a173 == 32)))) {
		a162 -= (a162 - 20) < a162 ? 1 : 0;
		cf = 0;
		a320 = (a206 - -3);
		a312 = 33;
		a382 = (((((a382 * a201) % 107) + 58) + 2) + -82);
		a225 = a205[(a211 / a320)];
		a57 = a8;
		a228 = a229;
		a234 = a372[(a359 - 2)];
		a329 = 32;
		a270 = ((a237 - a237) - -12);
		a358 = a335;
		a211 = (a206 + -4);
		a260 = 1;
		a357 = ((((((((a357 * a243) % 14999) - -14894) % 38) + -35) * 5) % 38) + -17);
		a338 = (a270 - 9);
		a368 = 1;
		a296 = a212;
		a359 = ((a206 * a270) - 57);
		a75 = 34;
		a230 = ((a237 - a320) - -9);
		a201 = ((((((a201 * a277) % 94) + 83) + 2) + -12577) + 12574);
		a240 = 1;
		a324 = a232[(a237 + -2)];
		a143 = 34;
		a237 = ((a270 + a206) + -14);
		a339 = 1;
		a353 = a399;
		a373 = 0;
		a398 = (a206 + 7);
		a313 = 33;
		a265 = a376;
		a361 = 34;
		a202 = a217[(a270 - 10)];
		a173 = 33;
		a276 = a253;
		a206 = ((a320 - a398) - -8);
	}
	if (((a383 == a226[1] && (a75 == 32 && ((((11 == a353[4]) && a125 == a30[1]) && (43 == a392[3])) && a8 == 11))) && (a338 == 4 && (a237 == 4 && (((input == inputs[5] && cf == 1) && a173 == 32) && a324 == a232[1]))))) {
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		cf = 0;
		a324 = a232[((a211 + a211) + -2)];
		a75 = 34;
		a353 = a399;
		a240 = 1;
		a234 = a372[(a270 + -11)];
		a357 = (((((((a357 * a243) % 14999) % 38) + -55) * 5) % 38) - 15);
		a296 = a362;
		a137 = a189;
		a225 = a205[(a211 + -2)];
		a239 = a268;
		a57 = (a359 - -9);
		a359 = (a237 - -1);
		a313 = 33;
		a382 = (((((a382 * a386) / 5) % 107) - -96) + 14);
		a338 = (a230 - -1);
		a228 = a292;
		a386 = ((((((a386 * a277) - -222) % 61) + 262) + -3940) + 3942);
		a154 = (a57 - -2);
		a211 = ((a206 * a237) + -17);
		a276 = a250;
		a339 = 0;
		a206 = (a8 - 7);
		a237 = (a338 + -2);
	}
}
void calculate_outputm52(int input) {
	if (((a383 == a226[1] && (a368 != 1 && (a207 == 32 && (((a173 == 32 && (cf == 1 && a125 == a30[4])) && a210 != 1) && a313 == 32)))) && (((((-188 < a357) && (-57 >= a357)) && a75 == 32) && a206 == 5) && input == inputs[3]))) {
		a31 += (a31 + 20) > a31 ? 2 : 0;
		cf = 0;
		a218 = 33;
		a359 = (a398 - 8);
		a234 = a372[(a359 - 3)];
		a370 = a318;
		a276 = a253;
		a77 = ((a338 * a320) + -18);
		a310 = (((((a310 * a277) % 14999) - 4302) + -1566) * 1);
		a361 = 33;
		a320 = (a359 - -3);
		a230 = (a338 - 1);
		a132 = 0;
		a75 = 33;
		a395 = 1;
		a1 = a87[(a77 + -10)];
	}
	if (((a361 == 32 && ((a398 == 11 && ((a210 != 1 && (a75 == 32 && ((28 == a370[0]) && a234 == a372[1]))) && a378 != 1)) && a173 == 32)) && ((a125 == a30[4] && (input == inputs[9] && cf == 1)) && a368 != 1))) {
		cf = 0;
		if (((!(a207 == 36) && (a171 == 33 || !(a383 == 7))) && a324 == 15)) {
			a310 = ((((a382 * a382) / -5) * 5) - 6813);
			a370 = a318;
			a338 = (a270 + -8);
			a357 = (((((((a249 * a382) % 14999) + 584) - 8261) * 1) % 14906) - 15093);
			a202 = a217[(a320 + -7)];
			a383 = a226[(a338 - 3)];
			a295 = a366[a230];
			a307 = a227[((a270 + a230) - 13)];
			a218 = 33;
			a336 = 1;
			a277 = (((((((a249 * a249) % 14999) % 78) + 68) - 17204) * 1) + 17205);
			a235 = a216[(a230 - 3)];
			a224 = 33;
			a373 = 1;
			a276 = a253;
			a333 = (((((a310 * a357) % 14999) / 5) - 15709) + -1033);
			a240 = 1;
			a201 = (((((((a201 * a249) % 14999) - 11272) % 14900) - 15098) / 5) + -23975);
			a75 = 35;
			a339 = 1;
			a320 = (a230 + 2);
			a398 = (a230 - -6);
			a296 = a212;
			a239 = a268;
			a237 = (a206 + -2);
			a134 = 0;
			a184 = a157[(a359 + 3)];
			a206 = ((a270 - a338) + -4);
			a359 = (a270 - 8);
			a313 = 33;
			a353 = a399;
			a312 = 33;
			a302 = a346[(a398 - 9)];
		} else {
			a357 = (((((a357 * a243) % 38) + -55) / 5) - -21);
			a201 = (((((((a357 * a382) % 94) + 82) + 0) * 5) % 94) + 83);
			a269 = 34;
			a260 = 0;
			a218 = 34;
			a202 = a217[(a270 + -9)];
			a338 = (a230 - -1);
			a206 = (a230 - -2);
			a359 = a338;
			a358 = a335;
			a392 = a304;
			a75 = 34;
			a276 = a250;
			a143 = 32;
			a353 = a399;
			a277 = ((((((a243 * a357) - 7735) * 2) + 27084) % 95) - -233);
			a240 = 1;
			a320 = (a338 - -3);
			a398 = (a320 + 4);
			a310 = (((((((a310 * a201) % 14999) * 2) - 0) - -2) % 20) + 336);
			a239 = a268;
			a383 = a226[(a237 + -3)];
			a228 = a292;
			a270 = (a320 - -4);
			a230 = (a206 - 1);
			a224 = 34;
			a382 = ((((((a382 * a277) / 5) + -10956) + 13231) % 107) - -68);
			a57 = 11;
			a361 = 34;
			a307 = a227[(a338 - 3)];
			a14 = a79[(a57 + -9)];
		}
	}
}
void calculate_outputm54(int input) {
	if (((((77 < a386) && (201 >= a386)) && (((-65 < a382) && (-39 >= a382)) && ((a302 == a346[1] && (input == inputs[4] && ((cf == 1 && a125 == a30[5]) && a81 == a167[2]))) && a373 != 1))) && (((a75 == 32 && a230 == 4) && a173 == 32) && a206 == 5))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a162 -= (a162 - 20) < a162 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		if (a196 == 15) {
			a81 = a167[5];
		} else {
			a132 = 0;
			a77 = (a359 - -6);
			a75 = 33;
			a1 = a87[((a230 - a320) + 5)];
		}
	}
	if ((((a329 == 32 && a383 == a226[1]) && a75 == 32) && (a336 != 1 && ((40 == a239[3]) && ((76 == a358[5]) && (a173 == 32 && ((a125 == a30[5] && ((a81 == a167[2] && cf == 1) && input == inputs[8])) && a329 == 32))))))) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		if ((((a141 == 10 || (a378 != 1 && a260 == 1)) || 325 < a13) && (103 == a275[0]))) {
			a395 = 0;
			a240 = 0;
			a158 = ((a270 * a270) - 113);
			a357 = (((a357 + -4522) / 5) - 25588);
			a260 = 0;
			a324 = a232[1];
			a338 = 4;
			a235 = a216[3];
			a225 = a205[7];
			a243 = ((((a243 * 5) - -10835) - 22028) - -35515);
			a378 = 0;
			a230 = 3;
			a207 = 32;
			a202 = a217[3];
			a307 = a227[0];
			a382 = (((((a382 % 12) + -49) * 5) % 12) - 44);
			a75 = 34;
			a237 = 7;
			a373 = 1;
			a336 = 0;
			a57 = (a158 + 2);
			a218 = 33;
			a201 = (((a201 / 5) - -16357) + -9520);
			a239 = a242;
			a383 = a226[7];
			a81 = a167[((a57 / a158) + 4)];
		} else {
			a368 = 0;
			a240 = 0;
			a230 = 8;
			a75 = 35;
			a270 = 12;
			a260 = 0;
			a269 = 32;
			a228 = a292;
			a338 = 8;
			a206 = 11;
			a386 = ((((((a386 * 5) % 61) - -133) * 5) % 61) + 133);
			a383 = a226[5];
			a373 = 0;
			a320 = 8;
			a129 = a92[((a237 - a398) + 9)];
			a224 = 35;
			a277 = ((((89 - 25) - -4251) - -1938) - 6163);
			a333 = (((((a333 / 5) + -23187) - -1508) % 14) - -168);
			a196 = ((a237 - a237) - -10);
			a249 = ((((a249 - -13990) * 10) / 9) - -11139);
			a207 = 32;
			a237 = 9;
			a313 = 32;
			a276 = a250;
			a359 = 4;
			a134 = 1;
			a353 = a241;
			a398 = 16;
		}
	}
	if ((((((a75 == 32 && cf == 1) && a125 == a30[5]) && a173 == 32) && ((-65 < a382) && (-39 >= a382))) && (a237 == 4 && (((input == inputs[6] && (((77 < a386) && (201 >= a386)) && (((-199 < a201) && (-12 >= a201)) && (89 == a296[5])))) && a81 == a167[2]) && a270 == 11)))) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if (((a278 == 6 || !(a278 == a326[4])) || !(60 == a3[3]))) {
			a243 = (((a243 * 5) * 5) * -5);
			a256 = 32;
			a269 = 36;
			a224 = 33;
			a225 = a205[3];
			a234 = a372[3];
			a265 = a303;
			a312 = 35;
			a296 = a212;
			a329 = 36;
			a286 = a294[6];
			a338 = 3;
			a235 = a216[3];
			a339 = 1;
			a91 = (a230 + 7);
			a207 = 35;
			a173 = 35;
			a353 = a263;
			a1 = a87[((a91 / a91) - -5)];
		} else {
			a57 = 17;
			a40 = a65;
			a75 = 34;
			a141 = a47[((a57 - a57) + 6)];
		}
	}
	if (((((-199 < a201) && (-12 >= a201)) && ((76 == a358[5]) && (a173 == 32 && (a75 == 32 && a359 == 4)))) && (a237 == 4 && (a395 != 1 && (((a81 == a167[2] && (a125 == a30[5] && cf == 1)) && ((-65 < a382) && (-39 >= a382))) && input == inputs[1]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a249 = (((a249 - -23439) + 3664) * 1);
		a239 = a242;
		a368 = 0;
		a202 = a217[6];
		a224 = 35;
		a358 = a348;
		a225 = a205[2];
		a218 = 35;
		a234 = a372[7];
		a228 = a229;
		a256 = 32;
		a296 = a384;
		a383 = a226[6];
		a302 = a346[5];
		a125 = a30[(a270 - 4)];
		a339 = 1;
		a312 = 34;
		a398 = 11;
		a265 = a376;
		a333 = ((((a333 * 5) - 2890) - -15856) - 18991);
		a307 = a227[5];
		a129 = a92[7];
	}
	if (((a125 == a30[5] && (a230 == 4 && a302 == a346[1])) && ((((-188 < a357) && (-57 >= a357)) && (a240 != 1 && ((a398 == 11 && (a320 == 7 && (a75 == 32 && (a81 == a167[2] && cf == 1)))) && a173 == 32))) && input == inputs[5]))) {
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		a81 = a167[(a398 + -6)];
	}
	if (((((input == inputs[7] && (a173 == 32 && (((a81 == a167[2] && cf == 1) && a125 == a30[5]) && a218 == 32))) && a368 != 1) && a240 != 1) && ((((40 == a239[3]) && a75 == 32) && a398 == 11) && a329 == 32))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		a161 -= (a161 - 20) < a161 ? 1 : 0;
		cf = 0;
		a256 = 33;
		a206 = 9;
		a339 = 1;
		a357 = ((((a357 % 65) + -62) + 5) + -65);
		a57 = 13;
		a240 = 0;
		a137 = a116;
		a383 = a226[1];
		a310 = ((((a310 - -7812) * 10) / 9) * 3);
		a336 = 0;
		a243 = ((((a243 * 12) / 10) + -11071) + -10724);
		a211 = 2;
		a382 = ((((a382 * 10) / 6) - 1919) + -816);
		a260 = 0;
		a270 = 11;
		a295 = a366[(a338 + -2)];
		a358 = a351;
		a207 = 33;
		a265 = a376;
		a202 = a217[6];
		a286 = a294[4];
		a230 = 9;
		a373 = 0;
		a218 = 35;
		a228 = a264;
		a225 = a205[6];
		a368 = 0;
		a307 = a227[3];
		a386 = (((a386 * 5) / 5) + 23345);
		a329 = 35;
		a359 = 8;
		a237 = 10;
		a320 = 13;
		a296 = a384;
		a300 = 0;
		a361 = 32;
		a324 = a232[6];
		a312 = 33;
		a313 = 32;
		a302 = a346[5];
		a75 = 34;
		a378 = 0;
		a333 = ((((a333 % 96) - -50) - -1) - -1);
		a239 = a242;
		a249 = (((a249 / 5) - 13198) * 2);
		a398 = 14;
		a338 = 7;
	}
	if (((((a81 == a167[2] && ((76 == a358[5]) && a202 == a217[1])) && a173 == 32) && a270 == 11) && (((152 < a249) && (355 >= a249)) && (((((cf == 1 && a75 == 32) && a125 == a30[5]) && a300 != 1) && input == inputs[3]) && a324 == a232[1])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 3 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if ((a44 == 34 && (a234 == a372[3] || ((67 == a40[1]) && (a373 == 1 && a14 == 8))))) {
			a196 = (a211 - -13);
			a249 = (((((a249 * 5) + -18960) / 5) * -2) / 10);
			a235 = a216[3];
			a353 = a399;
			a265 = a293;
			a338 = 7;
			a256 = 35;
			a218 = 32;
			a224 = 34;
			a313 = 36;
			a361 = 34;
			a135 = 34;
			a373 = 0;
			a359 = 5;
			a382 = (((((a382 * 6) / 10) - -21) + 28356) - 28184);
			a75 = 35;
			a276 = a289;
			a206 = 5;
			a296 = a384;
			a234 = a372[7];
			a237 = 9;
			a240 = 0;
			a134 = 1;
			a228 = a292;
			a333 = ((((((a333 + -18287) % 14) - -172) * 5) % 14) - -157);
			a320 = 12;
			a368 = 0;
			a211 = 2;
		} else {
			a75 = 34;
			a57 = (a338 - -6);
			a81 = a167[((a230 - a320) + 6)];
			a158 = ((a338 / a57) + 8);
		}
	}
	if ((((a361 == 32 && ((a218 == 32 && (input == inputs[0] && (a125 == a30[5] && cf == 1))) && a75 == 32)) && (89 == a296[5])) && (a81 == a167[2] && ((((103 == a276[1]) && ((-179 < a243) && (-156 >= a243))) && a202 == a217[1]) && a173 == 32)))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		if (a243 <= -179) {
			a81 = a167[((a270 / a206) + 3)];
		} else {
			a307 = a227[7];
			a69 = 35;
			a382 = ((((a382 * 17) / 10) * 5) + -1006);
			a201 = ((((a201 / 5) * 5) + 11605) + -11844);
			a218 = 35;
			a296 = a384;
			a230 = 4;
			a249 = ((((a249 * -5) - -18696) * 1) + -20439);
			a75 = 34;
			a202 = a217[0];
			a143 = 36;
			a270 = 15;
			a240 = 0;
			a313 = 36;
			a359 = 10;
			a357 = ((((a357 - -26996) + -53642) + -497) - -39829);
			a57 = 11;
		}
	}
	if (((((input == inputs[9] && (a81 == a167[2] && (a307 == a227[1] && (28 == a370[0])))) && a359 == 4) && a395 != 1) && (((((a173 == 32 && cf == 1) && a125 == a30[5]) && a75 == 32) && (50 == a228[0])) && a336 != 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if ((((-39 < a382) && (176 >= a382)) || a14 == 8)) {
			a386 = (((a386 - -26914) - -2859) + 13);
			a286 = a294[1];
			a357 = ((((a357 * 33) / 10) / 5) + -20718);
			a211 = 5;
			a240 = 0;
			a295 = a366[a237];
			a358 = a351;
			a57 = 13;
			a243 = ((((((a243 % 11) + -166) * 1) / 5) * 49) / 10);
			a228 = a229;
			a137 = a116;
			a338 = 6;
			a239 = a299;
			a361 = 32;
			a392 = a208;
			a368 = 0;
			a373 = 1;
			a336 = 0;
			a395 = 0;
			a249 = (((a249 - 20912) - -16665) * 5);
			a206 = 4;
			a320 = 13;
			a329 = 36;
			a207 = 35;
			a313 = 36;
			a75 = 34;
			a302 = a346[1];
			a260 = 0;
			a382 = ((((a382 - 8430) - 941) - -38843) + -38868);
			a300 = 0;
			a307 = a227[6];
			a270 = 16;
			a276 = a289;
			a359 = 8;
			a398 = 14;
			a383 = a226[3];
			a225 = a205[7];
			a224 = 34;
			a339 = 1;
			a333 = ((((a333 % 96) + 50) / 5) * 5);
			a230 = 10;
			a310 = (((a310 - -27913) / 5) + -5377);
			a235 = a216[7];
			a324 = a232[1];
			a218 = 33;
			a370 = a318;
			a277 = ((((6 * 567) / 10) + -18261) - -38904);
			a256 = 36;
			a237 = 7;
		} else {
			a75 = 34;
			a141 = a47[(a230 - -1)];
			a72 = (((((a357 * a333) - 1550) - 893) % 14948) - 15051);
			a57 = (a338 - -11);
		}
	}
	if (((((-188 < a357) && (-57 >= a357)) && (a324 == a232[1] && (a235 == a216[1] && ((input == inputs[2] && a260 != 1) && a125 == a30[5])))) && (((77 < a386) && (201 >= a386)) && (a81 == a167[2] && (a398 == 11 && ((cf == 1 && a75 == 32) && a173 == 32)))))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a5 -= (a5 - 20) < a5 ? 3 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a224 = 35;
		a382 = ((((a382 * 5) * 10) / 9) * 5);
		a307 = a227[0];
		a302 = a346[7];
		a276 = a253;
		a353 = a399;
		a265 = a303;
		a235 = a216[0];
		a312 = 34;
		a225 = a205[4];
		a269 = 36;
		a173 = 34;
		a329 = 33;
		a105 = 34;
		a373 = 0;
		a239 = a299;
		a202 = a217[3];
		a249 = (((a249 / -5) * 5) - 22678);
		a243 = (((a243 / 5) - -19101) + -19232);
		a234 = a372[6];
		a339 = 1;
		a228 = a264;
		a383 = a226[1];
		a172 = (a398 - 6);
	}
}
void calculate_outputm58(int input) {
	if ((((a75 == 32 && ((a225 == a205[1] && a378 != 1) && a81 == a167[7])) && (11 == a353[4])) && (((((a125 == a30[5] && (input == inputs[0] && cf == 1)) && a173 == 32) && (103 == a276[1])) && a378 != 1) && a235 == a216[1]))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a98 -= (a98 - 20) < a98 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		if ((76 == a358[5])) {
			a313 = 32;
			a382 = (((a382 - -12945) + 6073) + 7638);
			a249 = (((a249 - -28373) / 5) - 5453);
			a310 = (((((a310 % 77) + 192) / 5) - 25669) + 25873);
			a228 = a264;
			a312 = 34;
			a230 = 8;
			a357 = (((((a357 / 5) * 9) / 10) - 5177) - -5171);
			a373 = 0;
			a329 = 35;
			a300 = 0;
			a353 = a399;
			a75 = 35;
			a134 = 1;
			a207 = 35;
			a383 = a226[1];
			a338 = 10;
			a243 = (((((a243 % 11) - 159) - -23025) * 1) - 23028);
			a333 = ((((a333 - -15362) * 10) / 9) * 1);
			a260 = 0;
			a320 = 7;
			a237 = 7;
			a386 = (((a386 - -22549) * 1) - -2110);
			a225 = a205[1];
			a392 = a304;
			a324 = a232[7];
			a240 = 0;
			a307 = a227[7];
			a206 = 7;
			a196 = (a270 + 1);
			a370 = a311;
			a277 = (((a277 - 3031) / 5) - -15904);
			a276 = a250;
			a211 = 7;
			a339 = 0;
			a202 = a217[2];
			a54 = (((((((68 * 36) / 10) * 10) / 9) + -1697) * -2) / 10);
			a395 = 0;
			a359 = 4;
			a239 = a299;
			a265 = a376;
			a296 = a362;
			a235 = a216[1];
			a336 = 0;
			a256 = 32;
			a269 = 34;
			a368 = 0;
			a201 = (((a201 + 28950) / 5) - -13724);
			a398 = 11;
			a218 = 35;
			a378 = 0;
			a270 = 16;
		} else {
			a336 = 1;
			a333 = (((a333 / 5) / 5) - 30);
			a211 = 4;
			a225 = a205[4];
			a224 = 34;
			a228 = a292;
			a249 = (((((a249 * 10) / 3) * 5) * 10) / 9);
			a339 = 1;
			a256 = 35;
			a269 = 32;
			a260 = 0;
			a277 = ((((a277 % 78) + 69) - 1) + 1);
			a373 = 1;
			a210 = 0;
			a312 = 36;
			a296 = a212;
			a235 = a216[0];
			a353 = a241;
			a243 = (((((a243 * 5) + -19460) * 1) % 11) + -166);
			a239 = a299;
			a302 = a346[3];
			a361 = 34;
			a234 = a372[7];
			a307 = a227[2];
			a237 = 9;
			a286 = a294[7];
			a125 = a30[(a206 - 1)];
		}
	}
	if ((((((28 == a370[0]) && (a81 == a167[7] && ((a75 == 32 && (a173 == 32 && cf == 1)) && a312 == 32))) && a359 == 4) && ((-199 < a201) && (-12 >= a201))) && ((a125 == a30[5] && (((77 < a386) && (201 >= a386)) && (11 == a353[4]))) && input == inputs[4]))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		a161 += (a161 + 20) > a161 ? 2 : 0;
		cf = 0;
		a296 = a384;
		a75 = 36;
		a239 = a268;
		a64 = 0;
		a324 = a232[4];
		a260 = 0;
		a240 = 0;
		a237 = 7;
		a202 = a217[6];
		a338 = 7;
		a230 = 6;
		a378 = 0;
		a339 = 0;
		a395 = 0;
		a218 = 35;
		a398 = 15;
		a357 = (((a357 - -29703) + 142) - -111);
		a333 = (((((a333 + -6828) % 14) - -164) - -4682) - 4673);
		a276 = a289;
		a146 = 0;
		a73 = ((((94 / 5) * 224) / 10) * 5);
	}
	if (((a286 == a294[1] && (((input == inputs[1] && ((a173 == 32 && ((-65 < a382) && (-39 >= a382))) && ((-47 < a333) && (147 >= a333)))) && a75 == 32) && a218 == 32)) && (((77 < a386) && (201 >= a386)) && ((a125 == a30[5] && (cf == 1 && a81 == a167[7])) && ((-10 < a277) && (148 >= a277)))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		cf = 0;
		if (((a244 == 5 && (!(a191 == a37[7]) && a7 == 1)) || a378 != 1)) {
			a373 = 0;
			a202 = a217[2];
			a239 = a299;
			a211 = 5;
			a228 = a264;
			a398 = 16;
			a134 = 0;
			a295 = a366[5];
			a218 = 35;
			a276 = a289;
			a336 = 0;
			a339 = 0;
			a392 = a304;
			a359 = 4;
			a296 = a384;
			a75 = 35;
			a333 = ((((a333 * 5) % 96) - -50) + 2);
			a269 = 34;
			a320 = 11;
			a53 = ((((63 + 19014) - 23799) - 18445) - -23186);
		} else {
			a75 = 33;
			a132 = 0;
			a77 = (a211 - -8);
			a1 = a87[a211];
		}
	}
	if (((a373 != 1 && ((((input == inputs[7] && ((-188 < a357) && (-57 >= a357))) && a125 == a30[5]) && a173 == 32) && (28 == a370[0]))) && ((a312 == 32 && ((a75 == 32 && (a81 == a167[7] && cf == 1)) && (89 == a296[5]))) && ((-188 < a357) && (-57 >= a357))))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		cf = 0;
		if (((26 < a170) && (82 >= a170))) {
			a361 = 35;
			a269 = 33;
			a225 = a205[4];
			a353 = a241;
			a265 = a303;
			a224 = 35;
			a234 = a372[4];
			a302 = a346[4];
			a312 = 32;
			a358 = a348;
			a339 = 0;
			a81 = a167[(a359 - 2)];
		} else {
			a40 = a65;
			a57 = ((a338 + a230) - -9);
			a75 = 34;
			a141 = a47[((a57 / a57) + -1)];
		}
	}
	if ((((a307 == a227[1] && ((a339 != 1 && ((152 < a249) && (355 >= a249))) && (43 == a392[3]))) && a225 == a205[1]) && (input == inputs[5] && (((a235 == a216[1] && ((cf == 1 && a173 == 32) && a125 == a30[5])) && a81 == a167[7]) && a75 == 32)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 += (a122 + 20) > a122 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if (((((152 < a249) && (355 >= a249)) && a307 == 5) && a75 == 33)) {
			a211 = 4;
			a353 = a241;
			a373 = 0;
			a218 = 34;
			a382 = (((a382 + 20310) / 5) + -4108);
			a249 = ((((a249 / 5) / 5) / 5) - -351);
			a260 = 0;
			a75 = 33;
			a333 = ((((a333 - -20795) * 1) * 1) + -31709);
			a269 = 32;
			a312 = 32;
			a386 = ((((a386 / 5) * -5) * 10) / 9);
			a256 = 34;
			a370 = a285;
			a77 = (a237 - -7);
			a339 = 1;
			a359 = 7;
			a225 = a205[4];
			a286 = a294[1];
			a357 = (((a357 / 5) * 5) - 26037);
			a307 = a227[1];
			a320 = 9;
			a324 = a232[0];
			a338 = 10;
			a270 = 17;
			a230 = 6;
			a313 = 32;
			a378 = 0;
			a206 = 9;
			a368 = 0;
			a243 = (((a243 - 594) / 5) - -9101);
			a300 = 0;
			a310 = (((((a310 - 12251) % 77) + 300) / 5) - -194);
			a239 = a299;
			a228 = a264;
			a202 = a217[2];
			a296 = a384;
			a265 = a376;
			a336 = 0;
			a329 = 36;
			a276 = a289;
			a235 = a216[7];
			a395 = 0;
			a240 = 0;
			a132 = 0;
			a237 = 7;
			a99 = a26[(a77 + -4)];
		} else {
			a397 = a398;
			a125 = a30[(a397 - 8)];
		}
	}
	if (((a75 == 32 && ((a269 == 32 && (a125 == a30[5] && ((cf == 1 && a173 == 32) && input == inputs[8]))) && a286 == a294[1])) && (a81 == a167[7] && ((a240 != 1 && ((11 == a353[4]) && ((-188 < a357) && (-57 >= a357)))) && ((-179 < a243) && (-156 >= a243)))))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a169 -= (a169 - 20) < a169 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		if ((a210 != 1 || a134 == 1)) {
			a277 = (((a277 * 5) * 5) + 10038);
			a173 = 34;
			a302 = a346[6];
			a172 = (a206 / a230);
			a224 = 36;
			a234 = a372[3];
			a358 = a348;
			a228 = a292;
			a383 = a226[3];
			a361 = 33;
			a353 = a241;
			a129 = a92[(a172 + a172)];
		} else {
			a132 = 0;
			a77 = 10;
			a75 = 33;
			a1 = a87[(a270 + -9)];
		}
	}
	if (((a312 == 32 && (((a75 == 32 && (a202 == a217[1] && ((a125 == a30[5] && (a81 == a167[7] && cf == 1)) && input == inputs[9]))) && a237 == 4) && a398 == 11)) && ((a173 == 32 && a329 == 32) && (43 == a392[3])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		if (a132 == 1) {
			a57 = ((a230 / a270) + 11);
			a75 = 34;
			a143 = 32;
			a14 = a79[a359];
		} else {
			a57 = ((a270 - a320) - -8);
			a75 = 34;
			a81 = a167[((a359 + a57) + -16)];
			a99 = a26[((a57 - a338) - 7)];
		}
	}
	if ((((a339 != 1 && ((28 == a370[0]) && (a398 == 11 && (a218 == 32 && (a336 != 1 && (((152 < a249) && (355 >= a249)) && a81 == a167[7])))))) && a75 == 32) && (input == inputs[2] && (a125 == a30[5] && (cf == 1 && a173 == 32))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		a81 = a167[(a230 + -1)];
	}
	if (((((43 == a392[3]) && (a173 == 32 && (a81 == a167[7] && cf == 1))) && a395 != 1) && (((-47 < a333) && (147 >= a333)) && (a373 != 1 && (input == inputs[6] && (((a211 == 2 && a125 == a30[5]) && a313 == 32) && a75 == 32)))))) {
		a120 -= (a120 - 20) < a120 ? 4 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if ((!(a313 == 32) || (a183 == 33 || (18 == a39[0])))) {
			a57 = 10;
			a75 = 34;
			a158 = (a206 - -4);
			a3 = a114;
		} else {
			a134 = 1;
			a196 = ((a206 * a270) + -45);
			a75 = 35;
			a129 = a92[((a196 + a196) + -13)];
		}
	}
	if (((a75 == 32 && ((a81 == a167[7] && (input == inputs[3] && cf == 1)) && ((-65 < a382) && (-39 >= a382)))) && (a237 == 4 && ((103 == a276[1]) && ((a368 != 1 && (((50 == a228[0]) && a173 == 32) && (11 == a353[4]))) && a125 == a30[5]))))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a98 -= (a98 - 20) < a98 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a75 = 34;
		a143 = 36;
		a69 = 36;
		a57 = 11;
	}
}
void calculate_outputm59(int input) {
	if ((((((77 < a386) && (201 >= a386)) && (a107 == 33 && (cf == 1 && a75 == 32))) && input == inputs[8]) && (a230 == 4 && (a173 == 32 && ((((77 < a386) && (201 >= a386)) && ((103 == a276[1]) && (((-47 < a333) && (147 >= a333)) && ((-179 < a243) && (-156 >= a243))))) && a125 == a30[6]))))) {
		a122 -= (a122 - 20) < a122 ? 4 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		if ((!(98 == a276[2]) || cf == 1)) {
			a57 = (a338 - -8);
			a81 = a167[((a338 * a320) + -23)];
			a75 = 34;
			a170 = ((((53 * 9) / 10) * 5) - 203);
		} else {
			a72 = ((((51 / 5) * -104) / 10) + -19128);
			a141 = a47[(a398 + -6)];
			a75 = 34;
			a57 = (a237 + 11);
		}
	}
	if (((a269 == 32 && (a125 == a30[6] && (a368 != 1 && ((a75 == 32 && (cf == 1 && input == inputs[5])) && a173 == 32)))) && (a202 == a217[1] && (a240 != 1 && ((a206 == 5 && a107 == 33) && a286 == a294[1]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a174 += (a174 + 20) > a174 ? 4 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		a91 = a398;
		a173 = 35;
		a1 = a87[a359];
	}
	if ((((a173 == 32 && ((a368 != 1 && (((76 == a358[5]) && a368 != 1) && a302 == a346[1])) && a107 == 33)) && (103 == a276[1])) && (((a125 == a30[6] && (cf == 1 && input == inputs[2])) && a75 == 32) && a225 == a205[1]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		a168 += (a168 + 20) > a168 ? 2 : 0;
		cf = 0;
		if ((!(a211 == 8) || (a81 == a167[1] || 20 < a357))) {
			a91 = ((a359 + a359) + 3);
			a173 = 35;
			a1 = a87[((a270 * a359) + -41)];
		} else {
			a249 = ((((a249 % 71) - -425) - 10662) + 10598);
			a256 = 32;
			a313 = 32;
			a339 = 1;
			a57 = ((a359 - a398) + 20);
			a269 = 35;
			a154 = (a338 + 11);
			a357 = (((a357 + -15353) + -3816) + -1171);
			a300 = 0;
			a320 = 10;
			a225 = a205[3];
			a75 = 34;
			a307 = a227[5];
			a228 = a229;
			a218 = 32;
			a333 = ((((a333 + -13515) + -8091) * 10) / 9);
			a353 = a263;
			a324 = a232[1];
			a137 = a189;
			a211 = 2;
			a237 = 9;
			a240 = 0;
			a234 = a372[2];
			a265 = a376;
			a359 = 7;
			a368 = 0;
			a373 = 0;
			a386 = ((((a386 * 5) * 5) % 61) + 101);
			a361 = 36;
			a239 = a242;
			a235 = a216[5];
			a276 = a253;
			a206 = 5;
			a382 = (((a382 + 24628) - -2381) / 5);
			a338 = 8;
		}
	}
	if ((((((152 < a249) && (355 >= a249)) && (a206 == 5 && a107 == 33)) && a398 == 11) && (a339 != 1 && (a75 == 32 && (a237 == 4 && ((a173 == 32 && ((cf == 1 && input == inputs[7]) && a125 == a30[6])) && a324 == a232[1])))))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a35 += (a35 + 20) > a35 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		cf = 0;
		a107 = 34;
		a173 = 34;
		a172 = (a338 - -4);
	}
	if (((((a218 == 32 && a286 == a294[1]) && ((-179 < a243) && (-156 >= a243))) && a270 == 11) && (((43 == a392[3]) && (a107 == 33 && (a173 == 32 && (a125 == a30[6] && ((a75 == 32 && cf == 1) && input == inputs[9]))))) && a300 != 1))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a67 -= (a67 - 20) < a67 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		cf = 0;
		a75 = 33;
		a132 = 1;
		a123 = 1;
		a137 = a117;
	}
	if (((a107 == 33 && ((50 == a228[0]) && a240 != 1)) && (a173 == 32 && ((((-65 < a382) && (-39 >= a382)) && ((103 == a276[1]) && (((a75 == 32 && (cf == 1 && a125 == a30[6])) && input == inputs[4]) && ((-65 < a382) && (-39 >= a382))))) && a300 != 1)))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a174 += (a174 + 20) > a174 ? 4 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		if (((a338 == 10 || (!(a99 == a26[6]) || a230 == 4)) && a151 != 1)) {
			a329 = 34;
			a228 = a292;
			a336 = 1;
			a312 = 35;
			a378 = 1;
			a353 = a241;
			a296 = a362;
			a172 = (a359 - -3);
			a173 = 34;
			a99 = a26[(a359 - -2)];
		} else {
			a72 = ((((38 * 5) * 5) - -423) - 5276);
			a75 = 34;
			a141 = a47[(a230 - -1)];
			a57 = (a237 + 11);
		}
	}
	if (((((11 == a353[4]) && (a75 == 32 && ((cf == 1 && a173 == 32) && input == inputs[6]))) && (50 == a228[0])) && (a237 == 4 && (a368 != 1 && (((a125 == a30[6] && (28 == a370[0])) && a107 == 33) && a398 == 11))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a75 = 33;
		a123 = 1;
		a132 = 1;
		a137 = a117;
	}
	if ((((input == inputs[0] && ((a75 == 32 && a240 != 1) && a234 == a372[1])) && a234 == a372[1]) && (((-10 < a277) && (148 >= a277)) && (a240 != 1 && (((a125 == a30[6] && (cf == 1 && a173 == 32)) && a359 == 4) && a107 == 33))))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a63 -= (a63 - 20) < a63 ? 4 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		a173 = 33;
		a66 = 0;
		a130 = ((((78 + 152) + 27059) / 5) - 5269);
	}
	if (((((a218 == 32 && a235 == a216[1]) && a206 == 5) && a107 == 33) && (a125 == a30[6] && (((76 == a358[5]) && (((-65 < a382) && (-39 >= a382)) && (((input == inputs[3] && cf == 1) && a173 == 32) && a383 == a226[1]))) && a75 == 32)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if (((a141 == 10 && (24 == a370[2])) || a373 == 1)) {
			a310 = (((((a310 + -9959) % 77) - -240) / 5) + 252);
			a368 = 0;
			a243 = (((((a243 % 11) + -159) + -19274) - 8966) + 28232);
			a313 = 35;
			a265 = a303;
			a339 = 1;
			a370 = a318;
			a256 = 35;
			a333 = (((a333 / 5) * 5) - -15195);
			a373 = 1;
			a218 = 35;
			a207 = 32;
			a386 = ((((a386 + 6751) * 10) / 9) / 5);
			a57 = 13;
			a357 = (((((a357 * 5) % 65) - 87) * 10) / 9);
			a302 = a346[1];
			a235 = a216[7];
			a240 = 0;
			a137 = a116;
			a228 = a229;
			a324 = a232[4];
			a320 = 7;
			a383 = a226[7];
			a286 = a294[3];
			a276 = a289;
			a237 = 9;
			a239 = a299;
			a361 = 36;
			a75 = 34;
			a358 = a348;
			a395 = 0;
			a230 = 3;
			a398 = 13;
			a260 = 0;
			a392 = a257;
			a382 = (((a382 + 2623) + -6698) + 8985);
			a225 = a205[3];
			a269 = 35;
			a307 = a227[3];
			a296 = a212;
			a206 = 10;
			a300 = 0;
			a338 = 10;
			a234 = a372[1];
			a312 = 34;
			a353 = a263;
			a270 = 15;
			a249 = ((((a249 % 101) - -170) + -9860) - -9894);
			a378 = 1;
			a359 = 9;
			a211 = 4;
			a277 = (((((a277 * 5) % 78) + 68) + 16374) + -16371);
			a295 = a366[(a57 + -9)];
		} else {
			a359 = 6;
			a265 = a293;
			a249 = (((((a249 / -5) * 10) / 9) * 10) / 9);
			a368 = 0;
			a312 = 36;
			a16 = 1;
			a353 = a399;
			a270 = 14;
			a225 = a205[4];
			a358 = a351;
			a218 = 32;
			a361 = 34;
			a302 = a346[5];
			a373 = 0;
			a300 = 0;
			a202 = a217[3];
			a286 = a294[3];
			a228 = a292;
			a398 = 16;
			a206 = 5;
			a395 = 0;
			a207 = 34;
			a235 = a216[6];
			a383 = a226[6];
			a296 = a384;
			a75 = 36;
			a386 = ((((a386 / 5) + 225) * 10) / 9);
			a338 = 7;
			a237 = 10;
			a339 = 0;
			a224 = 36;
			a234 = a372[6];
			a256 = 36;
			a276 = a289;
			a336 = 0;
			a240 = 0;
			a260 = 0;
			a146 = 0;
			a243 = (((a243 * 5) + 25508) * 1);
			a333 = ((((a333 % 96) - -51) - -1) - 2);
			a357 = (((a357 - -21632) / 5) + 522);
			a277 = (((((a277 + -804) + -10045) + -11581) % 78) - -136);
			a239 = a299;
			a230 = 10;
			a324 = a232[2];
			a329 = 36;
			a73 = (((((65 * 29) / 10) + 81) + 13232) + -13233);
		}
	}
	if ((((53 == a265[5]) && (a75 == 32 && (a107 == 33 && (cf == 1 && input == inputs[1])))) && (a373 != 1 && (a230 == 4 && (a339 != 1 && (a125 == a30[6] && ((103 == a276[1]) && (a395 != 1 && a173 == 32)))))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a169 -= (a169 - 20) < a169 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if ((((355 < a249) && (499 >= a249)) || (!(40 == a239[3]) && (a71 == a175[2] && !(a1 == 9))))) {
			a329 = 34;
			a398 = 11;
			a256 = 36;
			a260 = 0;
			a383 = a226[3];
			a201 = ((((((a201 * 166) / 10) * 10) / 9) + 19066) + -44987);
			a339 = 1;
			a158 = (a270 + -6);
			a235 = a216[5];
			a240 = 0;
			a353 = a241;
			a239 = a299;
			a206 = 11;
			a324 = a232[1];
			a207 = 32;
			a202 = a217[0];
			a395 = 0;
			a75 = 34;
			a225 = a205[3];
			a358 = a348;
			a234 = a372[5];
			a386 = (((((a386 * 5) + 8186) - -13985) % 61) + 97);
			a357 = (((a357 / 5) - -21640) + 4577);
			a307 = a227[0];
			a200 = a115[(a338 - -3)];
			a57 = (a211 - -8);
			a378 = 1;
			a277 = (((a277 * 5) + -6109) * 4);
			a218 = 35;
			a338 = 8;
		} else {
			a243 = (((((a243 % 11) + -167) + 12987) / 5) - 2724);
			a201 = ((((((a201 + -21532) % 93) + -74) * 5) % 93) - 58);
			a207 = 33;
			a260 = 0;
			a225 = a205[0];
			a395 = 0;
			a373 = 1;
			a235 = a216[7];
			a378 = 0;
			a57 = ((a230 + a230) + 2);
			a353 = a241;
			a239 = a299;
			a237 = 4;
			a383 = a226[1];
			a307 = a227[4];
			a357 = ((((a357 + -28061) - -31451) + -9035) + 29443);
			a158 = ((a338 + a398) + -7);
			a324 = a232[3];
			a202 = a217[6];
			a240 = 0;
			a81 = a167[(a57 - 5)];
			a230 = 9;
			a218 = 32;
			a265 = a303;
			a75 = 34;
			a382 = ((((((a382 % 12) - 44) * 10) / 9) + -16664) + 16666);
			a338 = 6;
		}
	}
}
void calculate_outputm61(int input) {
	if ((((a286 == a294[1] && (a173 == 32 && (a202 == a217[1] && (76 == a358[5])))) && input == inputs[2]) && (a75 == 32 && (((a312 == 32 && (a129 == a92[2] && (a125 == a30[7] && cf == 1))) && (89 == a296[5])) && a206 == 5)))) {
		a178 += (a178 + 20) > a178 ? 4 : 0;
		cf = 0;
		a125 = a30[((a237 + a237) + -8)];
		a54 = ((((50 - 15819) * 1) - 2572) + 40357);
		a225 = a205[(a398 - 11)];
		a361 = 32;
		a383 = a226[((a320 + a230) + -11)];
	}
}
void calculate_outputm62(int input) {
	if (((((a75 == 32 && ((((77 < a386) && (201 >= a386)) && (a218 == 32 && (a129 == a92[5] && (a173 == 32 && cf == 1)))) && (103 == a276[1]))) && a125 == a30[7]) && (input == inputs[4] && (((50 == a228[0]) && (28 == a370[0])) && a225 == a205[1]))) && a89 == 9776)) {
		a169 -= (a169 - 20) < a169 ? 3 : 0;
		cf = 0;
		a173 = 34;
		a8 = (a359 - -2);
		a172 = ((a8 * a8) + -34);
	}
	if ((((a173 == 32 && (a125 == a30[7] && (input == inputs[0] && (a129 == a92[5] && (a75 == 32 && cf == 1))))) && (a320 == 7 && ((((a339 != 1 && a329 == 32) && a313 == 32) && (50 == a228[0])) && a359 == 4))) && a63 >= 3)) {
		a5 -= (a5 - 20) < a5 ? 3 : 0;
		cf = 0;
		a370 = a311;
		a336 = 1;
		a75 = 34;
		a310 = ((((((a310 * a386) % 14999) % 20) - -334) * 5) / 5);
		a329 = 34;
		a392 = a304;
		a240 = 1;
		a218 = 34;
		a228 = a292;
		a395 = 1;
		a183 = 35;
		a357 = ((((((a357 * a382) % 38) + -47) / 5) + 6071) + -6106);
		a307 = a227[(a320 + -5)];
		a312 = 34;
		a333 = ((((((a333 * a382) / 5) / 5) * 5) % 14) - -163);
		a57 = (a270 + 5);
		a224 = 34;
		a206 = (a359 - -2);
		a278 = a326[(a359 - -1)];
	}
	if ((((((76 == a358[5]) && (76 == a358[5])) && a312 == 32) && a202 == a217[1]) && (a302 == a346[1] && ((a125 == a30[7] && (a173 == 32 && (((a75 == 32 && cf == 1) && a129 == a92[5]) && input == inputs[9]))) && (103 == a276[1]))))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 2 : 0;
		a5 += (a5 + 20) > a5 ? 2 : 0;
		a93 += (a93 + 20) > a93 ? 2 : 0;
		a94 -= (a94 - 20) < a94 ? 4 : 0;
		a164 += (a164 + 20) > a164 ? 4 : 0;
		cf = 0;
		a333 = ((((((a333 * a249) % 14999) * 2) % 14976) - 15022) * 1);
		a243 = (((((a382 * a201) - -10673) * -1) / 10) / 5);
		a276 = a250;
		a336 = 1;
		a398 = (a320 + 3);
		a224 = 34;
		a237 = (a359 - 1);
		a230 = (a206 - 2);
		a202 = a217[(a359 - 3)];
		a324 = a232[((a359 + a398) - 14)];
		a240 = 1;
		a339 = 1;
		a265 = a376;
		a16 = 1;
		a353 = a263;
		a300 = 1;
		a146 = 0;
		a256 = 34;
		a270 = (a359 - -6);
		a228 = a229;
		a286 = a294[((a230 / a230) + 1)];
		a302 = a346[((a338 / a230) - -1)];
		a75 = 36;
		a207 = 33;
		a373 = 1;
		a206 = (a237 - -1);
		a329 = 33;
		a249 = ((((((a333 * a310) % 14999) - 2958) + -524) % 71) + 447);
		a338 = (a211 - -1);
		a358 = a348;
		a368 = 1;
		a277 = ((((((a243 * a357) % 14999) - -6675) - 28838) + 33595) - 28609);
		a260 = 1;
		a73 = ((((2 + 23998) + -23825) * 5) + -627);
		a239 = a242;
		a361 = 33;
		a378 = 1;
		a386 = (((((a386 * a243) % 14999) - 11640) - 2220) + -142);
		a383 = a226[(a359 + -4)];
		a312 = 33;
		a234 = a372[((a237 * a237) - 7)];
		a218 = 33;
		a235 = a216[(a211 + -2)];
		a225 = a205[(a211 - 2)];
		a395 = 1;
		a357 = (((((a357 * a277) % 14999) / 5) / 5) + -16271);
		a359 = ((a398 * a230) + -25);
	}
	if (((a320 == 7 && ((a324 == a232[1] && ((a125 == a30[7] && ((a75 == 32 && (cf == 1 && a129 == a92[5])) && input == inputs[6])) && a173 == 32)) && a240 != 1)) && (a270 == 11 && (a329 == 32 && a207 == 32)))) {
		a94 += (a94 + 20) > a94 ? 2 : 0;
		cf = 0;
		a207 = 33;
		a307 = a227[(a359 + -4)];
		a202 = a217[(a270 + -11)];
		a378 = 1;
		a184 = a157[((a230 / a237) + 2)];
		a373 = 1;
		a134 = 0;
		a336 = 1;
		a358 = a348;
		a201 = (((((a201 * a249) % 14999) + -10585) - -7017) - 7345);
		a218 = 33;
		a312 = 33;
		a320 = ((a230 - a338) - -6);
		a75 = 35;
		a269 = 33;
		a276 = a253;
		a295 = a366[((a338 / a359) - -3)];
		a333 = (((((((a333 * a249) % 14999) - -7315) * 1) + -8548) % 14976) - 15022);
		a228 = a229;
		a310 = ((((a310 * a382) + 15730) / 5) + -2814);
		a339 = 1;
		a359 = (a270 - 8);
	}
	if (((((a312 == 32 && a75 == 32) && a173 == 32) && a300 != 1) && ((a368 != 1 && (a359 == 4 && (((input == inputs[5] && (a125 == a30[7] && cf == 1)) && a129 == a92[5]) && ((152 < a249) && (355 >= a249))))) && a378 != 1))) {
		a131 += (a131 + 20) > a131 ? 2 : 0;
		a169 += (a169 + 20) > a169 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 2 : 0;
		a90 += (a90 + 20) > a90 ? 6 : 0;
		a110 += (a110 + 20) > a110 ? 2 : 0;
		a31 -= (a31 - 20) < a31 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 2 : 0;
		cf = 0;
		a300 = 0;
		a359 = (a398 - 7);
		a237 = ((a338 / a206) - -5);
		a358 = a335;
		a230 = (a338 - -1);
		a329 = 34;
		a370 = a311;
		a392 = a304;
		a235 = a216[((a338 / a359) - -1)];
		a277 = (((((((a310 * a310) % 14999) + -3778) / 5) - -15211) % 95) + 164);
		a260 = 1;
		a202 = a217[(a359 - 3)];
		a368 = 1;
		a333 = (((((((a201 * a201) % 14999) % 14) + 157) * 5) % 14) - -160);
		a276 = a250;
		a313 = 34;
		a137 = a189;
		a357 = (((((((a357 * a249) % 14999) - 3739) % 38) - -20) - 18043) + 18020);
		a225 = a205[((a398 * a398) + -142)];
		a296 = a362;
		a302 = a346[((a398 / a398) - -1)];
		a286 = a294[((a230 - a237) - -2)];
		a361 = 34;
		a269 = 32;
		a383 = a226[(a230 + -3)];
		a224 = 34;
		a324 = a232[(a398 - 10)];
		a320 = (a237 - -3);
		a207 = 34;
		a240 = 1;
		a270 = ((a398 - a206) + 5);
		a312 = 34;
		a382 = ((((((a382 * a333) % 107) - -170) - -29684) * 1) + -29724);
		a211 = (a359 + -2);
		a57 = (a206 - -8);
		a243 = ((((((a386 * a386) % 14999) + 7528) % 11) - 166) * 1);
		a338 = ((a211 / a270) + 5);
		a206 = (a359 + 1);
		a256 = 32;
		a395 = 1;
		a336 = 1;
		a249 = ((((((a249 * a386) % 14999) + -15641) * 1) % 71) - -431);
		a386 = ((((((a386 * a310) % 14999) % 61) - -239) + 3) - -8);
		a75 = 34;
		a154 = ((a57 * a57) + -153);
		a339 = 0;
		a218 = 34;
		a228 = a292;
		a373 = 0;
		a307 = a227[((a398 * a359) + -58)];
	}
	if ((((a230 == 4 && (((-47 < a333) && (147 >= a333)) && (a211 == 2 && (a230 == 4 && (a373 != 1 && (a129 == a92[5] && (input == inputs[1] && (a173 == 32 && a211 == 2)))))))) && (a75 == 32 && (cf == 1 && a125 == a30[7]))) && a165 == 4790)) {
		a162 -= (a162 - 20) < a162 ? 2 : 0;
		cf = 0;
		a57 = (a206 + 10);
		a75 = 34;
		a72 = (((((19 * 10) / -1) - -5491) * -1) / 10);
		a141 = a47[(a57 + -13)];
	}
	if (((((a173 == 32 && ((a302 == a346[1] && ((cf == 1 && a125 == a30[7]) && a129 == a92[5])) && a75 == 32)) && a338 == 4) && ((((a302 == a346[1] && a269 == 32) && a338 == 4) && input == inputs[8]) && a260 != 1)) && a174 <= 3)) {
		cf = 0;
		a129 = a92[(a206 + -4)];
	}
	if (((a237 == 4 && (a324 == a232[1] && a361 == 32)) && (a336 != 1 && (a260 != 1 && ((a125 == a30[7] && ((a75 == 32 && ((cf == 1 && a173 == 32) && a129 == a92[5])) && input == inputs[2])) && a300 != 1))))) {
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a178 += (a178 + 20) > a178 ? 2 : 0;
		cf = 0;
		a368 = 1;
		a333 = (((32 - 14748) - 1869) - -16753);
		a260 = 1;
		a336 = 1;
		a307 = a227[((a270 * a270) + -119)];
		a224 = 34;
		a361 = 34;
		a249 = ((((((((a333 * a333) % 14999) % 71) - -385) - 12) * 5) % 71) - -394);
		a386 = ((((((a333 * a333) % 14999) % 61) - -238) + -1) + 28);
		a312 = 34;
		a158 = (a359 - -1);
		a202 = a217[(a158 - 3)];
		a338 = a158;
		a235 = a216[(a270 + -9)];
		a378 = 1;
		a392 = a304;
		a310 = (((((((a310 * a386) % 14999) - 23298) + -6426) + -77) % 20) + 343);
		a359 = (a398 + -7);
		a276 = a253;
		a320 = (a338 - -3);
		a382 = ((((((a382 * a249) % 14999) % 107) - -69) + -1) / 5);
		a313 = 34;
		a286 = a294[((a158 - a211) - 1)];
		a228 = a229;
		a269 = 34;
		a211 = (a270 - 8);
		a358 = a335;
		a57 = ((a206 + a270) - 6);
		a300 = 1;
		a237 = a158;
		a357 = (((((((a357 * a277) % 14999) % 38) - 17) - 20972) / 5) + 4187);
		a75 = 34;
		a206 = (a398 - 6);
		a218 = 34;
		a324 = a232[((a158 / a398) + 2)];
		a302 = a346[((a398 + a398) - 22)];
		a339 = 0;
		a373 = 0;
		a230 = a158;
		a240 = 1;
		a329 = 34;
		a225 = a205[(a270 - 9)];
		a200 = a115[(a57 - 5)];
		a395 = 1;
		a201 = (((((((a201 * a243) % 14999) / 5) % 94) + 76) - 13495) + 13499);
		a296 = a362;
		a207 = 34;
		a370 = a318;
		a270 = (a158 - -7);
	}
}
void calculate_outputm63(int input) {
	if (((((a234 == a372[1] && ((a270 == 11 && a173 == 32) && a312 == 32)) && a230 == 4) && ((-47 < a333) && (147 >= a333))) && ((a75 == 32 && ((28 == a370[0]) && (a125 == a30[7] && (a129 == a92[6] && cf == 1)))) && input == inputs[2]))) {
		a174 += (a174 + 20) > a174 ? 3 : 0;
		cf = 0;
		a269 = 34;
		a302 = a346[(a230 + -2)];
		a228 = a292;
		a353 = a399;
		a202 = a217[((a359 * a338) - 14)];
		a296 = a362;
		a358 = a335;
		a398 = (a320 + 5);
		a368 = 1;
		a383 = a226[(a270 - 9)];
		a218 = 34;
		a239 = a268;
		a249 = (((((a243 * a310) % 14999) - 193) + -5892) / 5);
		a256 = 34;
		a307 = a227[(a320 - 5)];
		a333 = (((((a333 * a382) / 5) * 5) % 14) - -161);
		a129 = a92[(a359 + 3)];
	}
	if (((a361 == 32 && a270 == 11) && ((a129 == a92[6] && (((a173 == 32 && ((((input == inputs[5] && cf == 1) && a125 == a30[7]) && a359 == 4) && a75 == 32)) && a378 != 1) && (53 == a265[5]))) && a270 == 11))) {
		cf = 0;
		a218 = 34;
		a125 = a30[(a359 - 3)];
		a207 = 34;
		a239 = a268;
		a8 = 10;
		a329 = 34;
		a333 = ((((((a333 * a201) % 14976) - 15022) + 7494) * 1) + -7495);
		a286 = a294[(a270 - 9)];
		a265 = a376;
		a256 = 34;
		a336 = 1;
		a202 = a217[((a359 * a230) - 16)];
		a300 = 1;
		a211 = (a8 + -9);
		a395 = 1;
		a234 = a372[(a359 + -4)];
		a383 = a226[(a8 - 8)];
	}
}
void calculate_outputm64(int input) {
	if (((((((a173 == 32 && a329 == 32) && a395 != 1) && a129 == a92[7]) && a378 != 1) && a339 != 1) && (((((a75 == 32 && cf == 1) && input == inputs[2]) && a125 == a30[7]) && ((-188 < a357) && (-57 >= a357))) && a320 == 7))) {
		a5 += (a5 + 20) > a5 ? 1 : 0;
		cf = 0;
		a398 = ((a237 + a237) + 3);
		a225 = a205[(a230 - 3)];
		a125 = a30[(a206 + -1)];
		a210 = 0;
		a307 = a227[((a237 + a398) + -15)];
		a243 = (((((a310 * a382) % 43) + -68) + -5310) + 5276);
		a302 = a346[((a320 + a320) - 12)];
		a358 = a348;
		a202 = a217[(a359 + -3)];
		a286 = a294[(a237 - 3)];
		a312 = 34;
		a336 = 0;
		a373 = 0;
		a339 = 0;
		a269 = 33;
		a256 = 34;
		a277 = ((((a277 * a201) / 5) - 14331) - 8887);
		a368 = 0;
		a260 = 1;
		a296 = a362;
		a218 = 32;
		a239 = a242;
		a228 = a229;
		a383 = a226[(a237 + -3)];
		a333 = ((((((((a357 * a357) % 14999) % 14) + 157) * 5) - 10748) % 14) - -172);
		a353 = a263;
		a235 = a216[((a211 - a320) - -7)];
		a237 = ((a398 * a211) + -17);
		a211 = (a270 + -9);
	}
	if (((((((-188 < a357) && (-57 >= a357)) && ((a75 == 32 && cf == 1) && a129 == a92[7])) && a173 == 32) && a395 != 1) && (a225 == a205[1] && (a211 == 2 && (((a260 != 1 && input == inputs[4]) && a125 == a30[7]) && a237 == 4))))) {
		cf = 0;
		a154 = (a211 + 9);
		a336 = 1;
		a324 = a232[a211];
		a312 = 34;
		a137 = a189;
		a57 = (a359 - -9);
		a225 = a205[(a320 - 5)];
		a260 = 1;
		a230 = ((a270 / a211) - 2);
		a276 = a250;
		a237 = (a320 - 2);
		a310 = ((((((((a310 * a277) % 14999) % 20) + 337) / 5) * 5) % 20) + 322);
		a240 = 1;
		a338 = (a270 + -6);
		a382 = ((((((a382 * a201) + -14060) / 5) / 5) % 107) + 165);
		a277 = ((((((a277 * a333) % 95) - -244) * 5) % 95) - -214);
		a211 = (a320 + -4);
		a357 = (((((((a357 * a201) % 14999) % 38) - 27) + -20) * 10) / 9);
		a75 = 34;
		a300 = 1;
		a392 = a304;
		a329 = 34;
		a320 = (a270 + -3);
		a339 = 0;
		a359 = (a398 - 7);
	}
}
void calculate_outputm4(int input) {
	if (((((a206 == 5 && (a125 == a30[0] && cf == 1)) && ((-199 < a201) && (-12 >= a201))) && a373 != 1) && (a312 == 32 && (a207 == 32 && ((-188 < a357) && (-57 >= a357)))))) {
		if (((((a312 == 32 && (cf == 1 && 402 < a54)) && a269 == 32) && (53 == a265[5])) && (a378 != 1 && (a338 == 4 && a237 == 4)))) {
			calculate_outputm46(input);
		}
	}
	if (((((cf == 1 && a125 == a30[1]) && a225 == a205[1]) && ((-10 < a277) && (148 >= a277))) && ((((-10 < a277) && (148 >= a277)) && ((89 == a296[5]) && ((-65 < a382) && (-39 >= a382)))) && a302 == a346[1]))) {
		if (((((a270 == 11 && ((-199 < a201) && (-12 >= a201))) && (50 == a228[0])) && a302 == a346[1]) && (a312 == 32 && ((a8 == 10 && cf == 1) && a307 == a227[1])))) {
			calculate_outputm47(input);
		}
		if (((a234 == a372[1] && (a224 == 32 && ((a8 == 11 && cf == 1) && (50 == a228[0])))) && (((-179 < a243) && (-156 >= a243)) && ((76 == a358[5]) && ((77 < a386) && (201 >= a386)))))) {
			calculate_outputm48(input);
		}
	}
	if (((a218 == 32 && ((cf == 1 && a125 == a30[4]) && a202 == a217[1])) && (((a329 == 32 && a300 != 1) && (103 == a276[1])) && a218 == 32))) {
		if (((a378 != 1 && (a224 == 32 && (a395 != 1 && (a210 != 1 && cf == 1)))) && (((160 < a310) && (316 >= a310)) && (((-188 < a357) && (-57 >= a357)) && (53 == a265[5]))))) {
			calculate_outputm52(input);
		}
	}
	if ((((50 == a228[0]) && ((152 < a249) && (355 >= a249))) && (a286 == a294[1] && (a286 == a294[1] && (a270 == 11 && ((a125 == a30[5] && cf == 1) && a260 != 1)))))) {
		if (((a383 == a226[1] && ((cf == 1 && a81 == a167[2]) && a256 == 32)) && (((((-199 < a201) && (-12 >= a201)) && ((-47 < a333) && (147 >= a333))) && a329 == 32) && a207 == 32))) {
			calculate_outputm54(input);
		}
		if ((((40 == a239[3]) && (((-199 < a201) && (-12 >= a201)) && (53 == a265[5]))) && ((((-65 < a382) && (-39 >= a382)) && (((-10 < a277) && (148 >= a277)) && (a81 == a167[7] && cf == 1))) && (50 == a228[0])))) {
			calculate_outputm58(input);
		}
	}
	if (((a286 == a294[1] && ((a256 == 32 && ((152 < a249) && (355 >= a249))) && a206 == 5)) && ((((152 < a249) && (355 >= a249)) && (a125 == a30[6] && cf == 1)) && a398 == 11))) {
		if ((((43 == a392[3]) && (((152 < a249) && (355 >= a249)) && a224 == 32)) && ((a368 != 1 && (((-10 < a277) && (148 >= a277)) && (a107 == 33 && cf == 1))) && (76 == a358[5])))) {
			calculate_outputm59(input);
		}
	}
	if (((a286 == a294[1] && (a235 == a216[1] && a361 == 32)) && (a338 == 4 && (a230 == 4 && (a338 == 4 && (cf == 1 && a125 == a30[7])))))) {
		if ((((a129 == a92[2] && cf == 1) && a320 == 7) && (a398 == 11 && (((-188 < a357) && (-57 >= a357)) && (((89 == a296[5]) && a339 != 1) && a398 == 11))))) {
			calculate_outputm61(input);
		}
		if (((a240 != 1 && ((cf == 1 && a129 == a92[5]) && (50 == a228[0]))) && (a312 == 32 && ((50 == a228[0]) && (a320 == 7 && a338 == 4))))) {
			calculate_outputm62(input);
		}
		if ((((((-65 < a382) && (-39 >= a382)) && a373 != 1) && ((-179 < a243) && (-156 >= a243))) && ((a373 != 1 && (a336 != 1 && (a129 == a92[6] && cf == 1))) && a307 == a227[1]))) {
			calculate_outputm63(input);
		}
		if (((((a300 != 1 && ((-10 < a277) && (148 >= a277))) && a230 == 4) && a312 == 32) && (a270 == 11 && ((a129 == a92[7] && cf == 1) && a336 != 1)))) {
			calculate_outputm64(input);
		}
	}
}
void calculate_outputm65(int input) {
	if ((((a378 != 1 && ((28 == a370[0]) && ((a302 == a346[1] && ((input == inputs[0] && cf == 1) && a129 == a92[1])) && a75 == 32))) && (a172 == 1 && (((152 < a249) && (355 >= a249)) && (a173 == 34 && (a339 != 1 && ((160 < a310) && (316 >= a310))))))) && a164 <= 3)) {
		cf = 0;
		a277 = ((((((a310 * a382) / 5) + 26863) / 5) % 78) - 2);
		a191 = a37[((a172 * a230) + 1)];
		a324 = a232[((a338 + a320) - 10)];
		a173 = 33;
		a239 = a299;
		a130 = ((((7 / 5) - 12888) - -26632) + -19006);
	}
	if ((((a300 != 1 && (((((-47 < a333) && (147 >= a333)) && (((-179 < a243) && (-156 >= a243)) && (a173 == 34 && ((cf == 1 && a129 == a92[1]) && input == inputs[4])))) && a75 == 32) && a172 == 1)) && (((-47 < a333) && (147 >= a333)) && ((11 == a353[4]) && a225 == a205[1]))) && (a131 % 2 == 0))) {
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		cf = 0;
		a134 = 1;
		a75 = 34;
		a278 = a326[(a172 + 5)];
		a57 = (a172 - -15);
	}
	if (((a338 == 4 && a359 == 4) && (((a75 == 32 && (a172 == 1 && ((a173 == 34 && (((a129 == a92[1] && cf == 1) && input == inputs[1]) && a207 == 32)) && (43 == a392[3])))) && (89 == a296[5])) && ((152 < a249) && (355 >= a249))))) {
		a162 -= (a162 - 20) < a162 ? 1 : 0;
		cf = 0;
		a202 = a217[(a398 - 10)];
		a358 = a351;
		a383 = a226[(a320 + -7)];
		a234 = a372[(a237 - 2)];
		a373 = 0;
		a239 = a299;
		a125 = a30[(a172 + -1)];
		a225 = a205[(a230 + -4)];
		a324 = a232[(a270 + -10)];
		a353 = a399;
		a211 = ((a338 + a359) + -6);
		a361 = 32;
		a173 = 32;
		a224 = 33;
		a54 = (((51 - -19348) * 1) + -10525);
	}
	if (((a240 != 1 && (a302 == a346[1] && (a173 == 34 && (a172 == 1 && (a224 == 32 && ((((cf == 1 && a75 == 32) && a129 == a92[1]) && input == inputs[8]) && a336 != 1)))))) && (((77 < a386) && (201 >= a386)) && a320 == 7))) {
		a174 -= (a174 - 20) < a174 ? 2 : 0;
		a67 += (a67 + 20) > a67 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 4 : 0;
		cf = 0;
		if ((a71 == 2 && a172 == 4)) {
			a228 = a292;
			a358 = a335;
			a269 = 34;
			a201 = ((((((((a277 * a277) % 14999) % 94) + 56) * 9) / 10) - -5632) - 5665);
			a260 = 1;
			a310 = ((((((a201 * a201) % 14999) * 2) % 20) + 337) - -1);
			a296 = a212;
			a206 = ((a270 + a270) - 16);
			a386 = ((((((a249 * a310) % 14999) % 61) + 238) + -10469) + 10483);
			a329 = 34;
			a202 = a217[(a398 + -10)];
			a373 = 0;
			a368 = 1;
			a256 = 34;
			a230 = (a270 - 6);
			a218 = 34;
			a137 = a117;
			a307 = a227[((a270 / a172) - 9)];
			a313 = 34;
			a265 = a376;
			a75 = 34;
			a320 = (a230 - -1);
			a324 = a232[a172];
			a378 = 1;
			a243 = (((((((a243 * a386) % 14999) % 43) + -111) - -1) + 26436) - 26437);
			a357 = ((((((a357 * a333) % 38) + -17) * 5) % 38) + -17);
			a339 = 0;
			a224 = 34;
			a300 = 1;
			a211 = (a237 + -1);
			a333 = ((((((a310 * a310) % 14999) % 14) - -154) * 5) / 5);
			a276 = a250;
			a57 = (a172 + 12);
			a338 = (a206 + -1);
			a240 = 1;
			a336 = 1;
			a353 = a399;
			a234 = a372[(a398 - 9)];
			a392 = a304;
			a323 = (a172 - -6);
			a249 = (((((a249 * a382) / 5) + 17758) % 71) - -426);
			a359 = ((a237 / a172) - -1);
			a312 = 33;
			a398 = (a237 - -8);
			a237 = (a211 + 2);
			a207 = 34;
			a270 = (a323 - -5);
		} else {
			a202 = a217[(a320 + -6)];
			a339 = 1;
			a243 = (((((((a243 * a357) % 14999) % 43) - 123) * 5) % 43) + -106);
			a277 = ((((((a386 * a249) % 14999) - -14158) % 78) + -9) + 0);
			a358 = a351;
			a324 = a232[(a398 - 10)];
			a383 = a226[(a206 + -4)];
			a228 = a264;
			a353 = a399;
			a373 = 0;
			a129 = a92[((a237 * a359) - 9)];
			a234 = a372[((a270 * a338) - 42)];
			a239 = a299;
			a269 = 33;
			a211 = (a230 + -1);
		}
	}
	if ((((a172 == 1 && (((53 == a265[5]) && (((-188 < a357) && (-57 >= a357)) && ((cf == 1 && a129 == a92[1]) && input == inputs[7]))) && a329 == 32)) && (a75 == 32 && ((a225 == a205[1] && (((-65 < a382) && (-39 >= a382)) && a173 == 34)) && a398 == 11))) && a122 >= 3)) {
		a162 -= (a162 - 20) < a162 ? 3 : 0;
		cf = 0;
		a320 = (a237 + 2);
		a276 = a253;
		a392 = a208;
		a339 = 1;
		a224 = 33;
		a296 = a212;
		a361 = 33;
		a295 = a366[(a230 - -1)];
		a218 = 33;
		a336 = 1;
		a359 = ((a320 / a320) - -2);
		a134 = 0;
		a398 = ((a359 - a359) - -10);
		a75 = 35;
		a269 = 33;
		a333 = (((((a333 * a357) % 14976) - 15022) + -1) * 1);
		a239 = a242;
		a53 = ((((83 * -1) / 10) / 5) - 9);
	}
	if ((((((a302 == a346[1] && a398 == 11) && (89 == a296[5])) && a172 == 1) && (a307 == a227[1] && ((a173 == 34 && ((((cf == 1 && a75 == 32) && input == inputs[3]) && a129 == a92[1]) && a269 == 32)) && a361 == 32))) && a120 >= 3)) {
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		cf = 0;
		a225 = a205[((a230 / a237) + 1)];
		a158 = ((a270 - a172) - 5);
		a57 = ((a230 - a230) - -10);
		a357 = ((((((a357 * a386) % 14999) / 5) - -11951) % 38) + -22);
		a395 = 1;
		a392 = a304;
		a320 = ((a57 + a237) + -6);
		a243 = (((((((a243 * a310) % 14999) % 43) + -111) - 23244) * 1) - -23243);
		a338 = (a237 + 1);
		a207 = 34;
		a256 = 34;
		a353 = a399;
		a200 = a115[(a158 + 1)];
		a75 = 34;
		a339 = 0;
		a240 = 1;
		a218 = 34;
		a307 = a227[(a57 - 8)];
	}
}
void calculate_outputm66(int input) {
	if ((((a75 == 32 && ((103 == a276[1]) && ((((a172 == 1 && (input == inputs[3] && cf == 1)) && a207 == 32) && a173 == 34) && a225 == a205[1]))) && a129 == a92[2]) && ((a329 == 32 && a230 == 4) && a211 == 2))) {
		a51 -= (a51 - 20) < a51 ? 2 : 0;
		cf = 0;
		a224 = 33;
		a383 = a226[((a398 / a338) - 2)];
		a361 = 32;
		a125 = a30[(a172 - 1)];
		a173 = 32;
		a225 = a205[(a338 + -4)];
		a54 = (((17 - 8191) - 3009) - -25081);
	}
	if (((((((-179 < a243) && (-156 >= a243)) && ((160 < a310) && (316 >= a310))) && a129 == a92[2]) && input == inputs[4]) && (a361 == 32 && ((a173 == 34 && ((76 == a358[5]) && (((160 < a310) && (316 >= a310)) && ((a75 == 32 && cf == 1) && a172 == 1)))) && a395 != 1)))) {
		a165 += (a165 + 20) > a165 ? 4 : 0;
		a98 += (a98 + 20) > a98 ? 6 : 0;
		a94 += (a94 + 20) > a94 ? 1 : 0;
		cf = 0;
		a358 = a348;
		a239 = a268;
		a353 = a241;
		a324 = a232[a211];
		a373 = 1;
		a129 = a92[(a206 - 4)];
		a234 = a372[(a398 + -11)];
		a211 = ((a230 + a172) + -4);
		a202 = a217[((a398 * a398) - 121)];
	}
}
void calculate_outputm68(int input) {
	if (((a373 != 1 && (a240 != 1 && ((a75 == 32 && a235 == a216[1]) && a300 != 1))) && ((a172 == 1 && (((a173 == 34 && (a129 == a92[7] && cf == 1)) && a373 != 1) && input == inputs[9])) && (76 == a358[5])))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 2 : 0;
		a5 += (a5 + 20) > a5 ? 2 : 0;
		a93 += (a93 + 20) > a93 ? 2 : 0;
		a94 -= (a94 - 20) < a94 ? 4 : 0;
		a161 -= (a161 - 20) < a161 ? 4 : 0;
		cf = 0;
		a383 = a226[((a320 * a398) - 77)];
		a207 = 33;
		a296 = a212;
		a243 = (((((a310 * a310) % 14999) + 12236) + -41334) / 5);
		a211 = (a172 + 1);
		a270 = (a237 + 6);
		a206 = (a398 - 7);
		a324 = a232[(a230 + -4)];
		a269 = 32;
		a228 = a229;
		a338 = ((a230 * a270) + -37);
		a336 = 1;
		a256 = 34;
		a239 = a242;
		a333 = (((((a333 * a277) + -22052) * 1) - -29374) - 30340);
		a353 = a263;
		a235 = a216[(a270 - 10)];
		a368 = 1;
		a265 = a376;
		a302 = a346[(a398 - 9)];
		a218 = 33;
		a276 = a250;
		a73 = ((((((51 * 10) / 3) - -14) * 5) * 2) / 10);
		a224 = 34;
		a361 = 33;
		a357 = (((((a357 * a310) % 14999) + -4466) - 6371) - 3684);
		a300 = 1;
		a386 = (((((a386 * a249) % 14999) - 20028) * 1) * 1);
		a225 = a205[((a172 + a230) - 5)];
		a240 = 1;
		a249 = (((((((a243 * a243) % 14999) + -20214) - 2084) + 30808) % 71) + 381);
		a373 = 1;
		a277 = (((((a243 * a310) % 14999) + -9328) + 22102) - 26900);
		a146 = 0;
		a329 = 33;
		a75 = 36;
		a260 = 1;
		a237 = ((a398 - a206) + -4);
		a286 = a294[(a270 + -8)];
		a378 = 1;
		a312 = 33;
		a358 = a348;
		a398 = (a359 + 6);
		a359 = (a338 + 2);
		a234 = a372[((a338 / a270) + 2)];
		a395 = 1;
		a16 = 1;
		a230 = (a172 + 2);
		a202 = a217[(a338 + -2)];
	}
	if ((((a173 == 34 && ((40 == a239[3]) && ((cf == 1 && a75 == 32) && a172 == 1))) && (((a312 == 32 && ((a240 != 1 && (input == inputs[0] && a313 == 32)) && a129 == a92[7])) && a359 == 4) && a359 == 4)) && a63 >= 3)) {
		a162 -= (a162 - 20) < a162 ? 3 : 0;
		cf = 0;
		a395 = 1;
		a357 = (((((((a249 * a277) % 14999) - 5355) % 38) + -18) - -27153) + -27152);
		a183 = 35;
		a256 = 34;
		a240 = 1;
		a312 = 34;
		a218 = 34;
		a278 = a326[((a237 / a206) + 5)];
		a310 = (((((a357 * a357) % 20) + 336) - 10752) + 10753);
		a392 = a304;
		a224 = 34;
		a228 = a292;
		a239 = a268;
		a336 = 1;
		a370 = a311;
		a333 = ((((((a333 * a310) % 14999) - 10182) + -2893) % 14) + 163);
		a57 = (a230 - -12);
		a398 = (a320 - -5);
		a206 = (a359 - -2);
		a329 = 34;
		a75 = 34;
		a307 = a227[(a270 + -9)];
	}
	if ((((a129 == a92[7] && (a398 == 11 && (a359 == 4 && (a260 != 1 && (a270 == 11 && a172 == 1))))) && ((a378 != 1 && (((cf == 1 && a75 == 32) && input == inputs[8]) && a336 != 1)) && a173 == 34)) && a174 <= 3)) {
		cf = 0;
		a173 = 32;
		a129 = a92[((a359 + a270) + -14)];
		a125 = a30[(a237 - -3)];
	}
	if ((((a320 == 7 && ((50 == a228[0]) && a129 == a92[7])) && a240 != 1) && (a240 != 1 && (a172 == 1 && ((((77 < a386) && (201 >= a386)) && (((cf == 1 && input == inputs[5]) && a173 == 34) && a75 == 32)) && (53 == a265[5])))))) {
		a131 += (a131 + 20) > a131 ? 2 : 0;
		a169 += (a169 + 20) > a169 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 2 : 0;
		a90 += (a90 + 20) > a90 ? 6 : 0;
		a110 += (a110 + 20) > a110 ? 2 : 0;
		a31 -= (a31 - 20) < a31 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 2 : 0;
		a63 -= (a63 - 20) < a63 ? 4 : 0;
		cf = 0;
		a154 = ((a270 * a172) + 5);
		a57 = (a154 + -3);
		a333 = (((((((a333 * a310) % 14999) * 2) % 14) + 163) / 5) - -123);
		a206 = (a57 + -7);
		a307 = a227[((a237 / a237) + 1)];
		a383 = a226[(a154 - 14)];
		a202 = a217[(a237 - 2)];
		a269 = 32;
		a75 = 34;
		a302 = a346[(a154 + -14)];
		a336 = 1;
		a256 = 32;
		a239 = a268;
		a320 = (a237 + a230);
		a338 = ((a206 + a398) + -12);
		a224 = 34;
		a359 = (a211 + 2);
		a361 = 34;
		a260 = 1;
		a324 = a232[(a206 + -4)];
		a249 = (((((((a249 * a386) % 14999) / 5) - -8639) - -11158) % 71) + 374);
		a137 = a189;
		a230 = (a57 - 8);
		a218 = 34;
		a368 = 1;
		a395 = 1;
		a313 = 34;
		a235 = a216[(a320 + -7)];
		a392 = a304;
		a382 = (((((((a333 * a333) % 14999) % 107) + 31) - -1854) / 5) - 343);
		a296 = a362;
		a300 = 0;
		a243 = ((((((a277 * a386) / 5) % 11) + -166) - 23028) - -23027);
		a228 = a292;
		a286 = a294[(a398 - 9)];
		a240 = 1;
		a339 = 0;
		a270 = (a206 - -6);
		a329 = 34;
		a386 = (((((((a386 * a357) % 14999) % 61) + 262) + 0) - 16513) + 16514);
		a358 = a335;
		a373 = 0;
		a398 = ((a57 - a237) - -3);
		a225 = a205[(a154 - 14)];
		a370 = a311;
		a357 = (((((a357 * a277) + 9573) % 38) - 17) + -1);
		a265 = a376;
		a312 = 34;
		a276 = a250;
		a277 = (((((((a277 * a249) % 14999) % 95) + 243) + 0) - -20331) - 20330);
		a207 = 34;
		a237 = ((a320 / a338) - -4);
	}
	if (((((50 == a228[0]) && (a237 == 4 && (a260 != 1 && (input == inputs[2] && (a173 == 34 && (a129 == a92[7] && cf == 1)))))) && a75 == 32) && ((a172 == 1 && (a256 == 32 && a338 == 4)) && ((-47 < a333) && (147 >= a333))))) {
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a164 += (a164 + 20) > a164 ? 3 : 0;
		cf = 0;
		a218 = 34;
		a235 = a216[((a237 - a211) - -1)];
		a270 = (a338 + 8);
		a339 = 0;
		a370 = a318;
		a395 = 1;
		a373 = 0;
		a225 = a205[((a211 / a320) - -2)];
		a368 = 1;
		a386 = ((((((a243 * a243) % 61) + 252) * 5) % 61) - -238);
		a398 = (a237 - -8);
		a392 = a304;
		a260 = 1;
		a256 = 34;
		a358 = a335;
		a228 = a229;
		a307 = a227[((a211 + a320) - 8)];
		a383 = a226[((a270 + a359) - 14)];
		a57 = ((a172 - a320) - -16);
		a359 = (a320 + -2);
		a206 = (a211 + 3);
		a239 = a268;
		a200 = a115[(a320 + -2)];
		a265 = a376;
		a202 = a217[(a211 + -1)];
		a382 = (((((a243 * a243) % 107) - 4) - 7) + 34);
		a158 = (a57 - 5);
		a201 = ((((((a243 * a243) + -25483) - 6659) * 1) % 94) - -148);
		a324 = a232[(a230 + -2)];
		a207 = 34;
		a312 = 34;
		a302 = a346[(a211 + -1)];
		a333 = (((((((a333 * a310) % 14999) % 14) - -161) + 0) + 9652) - 9649);
		a336 = 1;
		a75 = 34;
		a361 = 34;
		a357 = (((((((a201 * a201) % 14999) % 38) - 18) + -28701) * 1) + 28700);
		a276 = a253;
		a338 = (a320 + -2);
		a378 = 1;
		a249 = ((((((a249 * a386) % 14999) - 22008) % 71) - -478) + -26);
		a296 = a362;
		a300 = 1;
		a277 = (((((a277 * a382) % 95) + 244) - -23732) - 23731);
		a237 = (a320 - 2);
		a269 = 34;
		a286 = a294[(a270 + -10)];
		a224 = 34;
		a329 = 34;
		a230 = (a211 + 2);
		a313 = 34;
		a310 = ((((((a357 * a357) % 20) - -337) + 1) / 5) + 259);
		a240 = 1;
		a320 = (a398 + -4);
	}
	if (((((43 == a392[3]) && (a300 != 1 && ((a173 == 34 && ((a172 == 1 && (cf == 1 && a75 == 32)) && a129 == a92[7])) && ((-47 < a333) && (147 >= a333))))) && (a312 == 32 && (a378 != 1 && (a336 != 1 && input == inputs[1])))) && a165 == 4790)) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		cf = 0;
		a75 = 34;
		a141 = a47[(a320 + -5)];
		a72 = (((((80 * 5) + -24070) + 48533) * -1) / 10);
		a57 = ((a270 * a172) + 4);
	}
	if (((((input == inputs[4] && (a368 != 1 && ((a172 == 1 && (cf == 1 && a75 == 32)) && (50 == a228[0])))) && a207 == 32) && (a129 == a92[7] && (((-10 < a277) && (148 >= a277)) && ((a173 == 34 && a383 == a226[1]) && (89 == a296[5]))))) && a89 == 9776)) {
		a174 += (a174 + 20) > a174 ? 3 : 0;
		cf = 0;
		a8 = (a237 + 2);
		a172 = (a320 - 5);
	}
	if (((((152 < a249) && (355 >= a249)) && (((89 == a296[5]) && a324 == a232[1]) && a230 == 4)) && ((a129 == a92[7] && ((a206 == 5 && (input == inputs[6] && (a75 == 32 && (a173 == 34 && cf == 1)))) && a172 == 1)) && (40 == a239[3])))) {
		a63 -= (a63 - 20) < a63 ? 1 : 0;
		cf = 0;
		a358 = a348;
		a228 = a229;
		a224 = 33;
		a75 = 35;
		a184 = a157[(a172 + 2)];
		a218 = 33;
		a378 = 1;
		a312 = 33;
		a207 = 33;
		a310 = ((((((a310 * a249) % 14999) - 18907) * 1) * 10) / 9);
		a333 = (((((a333 * a386) % 14976) - 15022) - 2) - 1);
		a295 = a366[a359];
		a307 = a227[((a398 - a230) + -7)];
		a320 = (a270 + -5);
		a134 = 0;
		a336 = 1;
		a276 = a253;
		a202 = a217[((a359 + a206) - 9)];
		a359 = ((a206 - a338) + 2);
		a296 = a212;
		a373 = 1;
		a201 = ((((a277 * a277) + -25161) - -22330) + -21383);
	}
}
void calculate_outputm72(int input) {
	if (((a172 == 5 && (a75 == 32 && ((a105 == 33 && ((77 < a386) && (201 >= a386))) && a329 == 32))) && (a336 != 1 && (((a339 != 1 && (input == inputs[3] && (cf == 1 && a173 == 34))) && (28 == a370[0])) && a224 == 32)))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		a161 -= (a161 - 20) < a161 ? 3 : 0;
		cf = 0;
		if (a383 == 11) {
			a125 = a30[(a320 - 6)];
			a173 = 32;
			a8 = (a172 - -7);
		} else {
			a269 = 32;
			a277 = (((3 + 20348) * 1) - -4048);
			a81 = a167[((a359 - a270) - -9)];
			a57 = ((a237 + a172) + 3);
			a312 = 32;
			a336 = 0;
			a358 = a351;
			a243 = ((((38 - 17724) / 5) / 5) * -5);
			a382 = (((((a382 / 5) - -26748) + -43333) * -1) / 10);
			a270 = 11;
			a307 = a227[1];
			a235 = a216[0];
			a324 = a232[3];
			a249 = (((a249 - -20824) - 22615) / 5);
			a339 = 0;
			a207 = 33;
			a240 = 0;
			a225 = a205[3];
			a158 = (a57 + -8);
			a378 = 0;
			a313 = 35;
			a386 = ((((a386 + -16466) * 10) / 9) * 1);
			a368 = 0;
			a224 = 32;
			a201 = (((91 + -29535) + 29286) - -21);
			a329 = 35;
			a230 = 8;
			a218 = 35;
			a75 = 34;
			a296 = a384;
			a234 = a372[6];
			a353 = a241;
			a361 = 33;
			a206 = 9;
			a302 = a346[7];
			a228 = a229;
			a398 = 10;
			a373 = 1;
			a300 = 0;
			a211 = 4;
			a256 = 35;
			a320 = 6;
			a310 = ((((a310 + 12610) % 77) + 196) - -5);
			a359 = 8;
			a276 = a289;
			a333 = ((((59 / 5) + 21053) - 42683) + 21645);
			a338 = 10;
			a265 = a293;
			a392 = a257;
			a357 = (((((a357 * 10) / 3) - 6970) * 10) / 9);
			a370 = a285;
			a239 = a242;
			a237 = 7;
		}
	}
	if (((a269 == 32 && (a218 == 32 && (a240 != 1 && (a173 == 34 && ((43 == a392[3]) && (input == inputs[4] && (cf == 1 && a105 == 33))))))) && (((-65 < a382) && (-39 >= a382)) && ((a172 == 5 && a235 == a216[1]) && a75 == 32)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		if (((a1 == 5 || (a230 == 6 && !(a383 == a226[5]))) && a36 <= 155)) {
			a137 = a117;
			a239 = a299;
			a378 = 0;
			a313 = 32;
			a269 = 33;
			a57 = ((a211 - a320) + 18);
			a323 = (a206 + 2);
			a398 = 16;
			a373 = 1;
			a75 = 34;
			a276 = a289;
			a201 = (((78 - -23929) * 1) - -5203);
			a300 = 0;
			a310 = (((a310 * -5) + -21076) / 5);
			a386 = (((a386 + 4113) - -17560) - 43948);
			a207 = 32;
			a224 = 35;
			a357 = ((((a357 - 24946) * 10) / 9) / 5);
			a307 = a227[6];
			a359 = 6;
			a230 = 10;
			a240 = 0;
			a237 = 9;
			a249 = ((((a249 - 25942) * 1) + 44138) + -25851);
			a353 = a241;
			a277 = (((37 + -22867) / 5) - -4561);
			a320 = 10;
			a265 = a293;
			a243 = (((13 + 29829) + 76) - -1);
			a270 = 13;
			a234 = a372[4];
			a296 = a384;
			a338 = 8;
			a302 = a346[6];
			a256 = 32;
			a218 = 33;
			a202 = a217[0];
			a358 = a351;
			a368 = 0;
			a333 = (((13 + -26148) - 1921) - 343);
			a336 = 0;
			a206 = 4;
			a329 = 32;
			a260 = 0;
			a392 = a257;
			a228 = a264;
			a339 = 1;
			a211 = 6;
		} else {
			a359 = 3;
			a57 = (a338 - -12);
			a361 = 35;
			a277 = (((81 / 5) * 5) / 5);
			a237 = 8;
			a235 = a216[5];
			a368 = 0;
			a270 = 15;
			a206 = 7;
			a286 = a294[5];
			a218 = 36;
			a310 = (((a310 / 5) + 14874) * 2);
			a378 = 0;
			a373 = 1;
			a228 = a292;
			a265 = a293;
			a201 = ((((10 * -91) / 10) + 9) + -24);
			a75 = 34;
			a243 = (((95 * 5) + -12773) + -5358);
			a320 = 10;
			a207 = 32;
			a357 = ((((a357 + 10966) + -6827) * 10) / 9);
			a278 = a326[(a172 + a211)];
			a239 = a242;
			a398 = 14;
			a392 = a257;
			a224 = 32;
			a307 = a227[3];
			a395 = 0;
			a353 = a263;
			a260 = 0;
			a313 = 36;
			a302 = a346[5];
			a333 = (((19 - 7418) / 5) + 17769);
			a256 = 35;
			a336 = 0;
			a386 = ((((a386 / 5) + 26185) + -17279) + -38222);
			a269 = 32;
			a249 = ((((((a249 + 465) * 10) / 9) / 5) * 37) / 10);
			a300 = 0;
			a230 = 6;
			a339 = 0;
			a81 = a167[(a172 - a172)];
			a329 = 32;
			a240 = 0;
			a324 = a232[4];
			a338 = 6;
			a225 = a205[4];
			a296 = a384;
			a234 = a372[0];
			a211 = 2;
		}
	}
	if ((((a307 == a227[1] && ((a234 == a372[1] && ((a173 == 34 && (a218 == 32 && (89 == a296[5]))) && a235 == a216[1])) && a75 == 32)) && a105 == 33) && (((cf == 1 && a172 == 5) && input == inputs[2]) && a395 != 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a67 -= (a67 - 20) < a67 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		cf = 0;
		if ((405 < a19 && ((a71 == a175[5] && a102 == 12) && !(a1 == 6)))) {
			a57 = (a172 + 11);
			a75 = 34;
			a107 = 32;
			a278 = a326[((a57 / a57) - -3)];
		} else {
			a243 = ((((82 + -15026) * 10) / 9) - 10923);
			a207 = 32;
			a173 = 36;
			a202 = a217[0];
			a256 = 35;
			a302 = a346[2];
			a386 = (((((a386 * 5) / 5) + -324) % 61) + 142);
			a230 = 7;
			a383 = a226[6];
			a336 = 0;
			a237 = 3;
			a312 = 33;
			a358 = a348;
			a221 = 1;
			a211 = 8;
			a353 = a263;
			a141 = a47[a338];
		}
	}
	if ((((a398 == 11 && (a75 == 32 && (((input == inputs[7] && cf == 1) && a105 == 33) && a172 == 5))) && a260 != 1) && (a234 == a372[1] && (a218 == 32 && ((a235 == a216[1] && a225 == a205[1]) && a173 == 34))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a168 += (a168 + 20) > a168 ? 4 : 0;
		cf = 0;
		if (((a300 == 1 || (((24 == a370[2]) || a260 == 1) && !(a329 == 36))) && !(a155 == 33))) {
			a173 = 36;
			a141 = a47[(a172 + -4)];
			a42 = (a211 - 1);
		} else {
			a211 = 6;
			a260 = 0;
			a386 = (((a386 + 14074) * 2) - -958);
			a224 = 35;
			a75 = 33;
			a296 = a384;
			a313 = 35;
			a239 = a299;
			a132 = 0;
			a228 = a264;
			a218 = 34;
			a234 = a372[1];
			a339 = 0;
			a276 = a250;
			a16 = 1;
			a361 = 32;
			a307 = a227[1];
			a373 = 0;
			a240 = 0;
			a368 = 0;
			a336 = 0;
			a201 = (((42 * 5) + -388) - -8);
			a206 = 10;
			a286 = a294[6];
			a320 = 8;
			a359 = 6;
			a249 = ((((a249 % 101) + 187) * 5) / 5);
			a378 = 0;
			a235 = a216[6];
			a370 = a285;
			a277 = (((57 / 5) - -23643) - -6152);
			a392 = a304;
			a207 = 34;
			a237 = 7;
			a353 = a399;
			a270 = 11;
			a202 = a217[1];
			a398 = 14;
			a383 = a226[6];
			a395 = 0;
			a357 = ((((a357 - -25182) - 38704) % 65) + -85);
			a310 = (((((a310 - -8145) + -2088) - 12762) * -1) / 10);
			a338 = 7;
			a256 = 34;
			a269 = 36;
			a302 = a346[7];
			a225 = a205[1];
			a77 = (a172 + 4);
		}
	}
	if (((a105 == 33 && ((11 == a353[4]) && ((a218 == 32 && (a207 == 32 && a75 == 32)) && a313 == 32))) && (a237 == 4 && ((53 == a265[5]) && (((cf == 1 && a172 == 5) && input == inputs[5]) && a173 == 34))))) {
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a173 = 35;
		a1 = a87[(a172 - 2)];
		a91 = a270;
	}
	if (((a373 != 1 && (a75 == 32 && (a256 == 32 && a395 != 1))) && (((((50 == a228[0]) && ((input == inputs[8] && (a173 == 34 && cf == 1)) && a172 == 5)) && a105 == 33) && a329 == 32) && a237 == 4))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 4 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		if ((((100 < a72) && (258 >= a72)) && ((a277 <= -10 || !(a269 == 34)) && !(a71 == a175[2])))) {
			a338 = 7;
			a256 = 32;
			a75 = 35;
			a320 = 13;
			a359 = 9;
			a276 = a289;
			a211 = 5;
			a249 = ((((a249 * 33) / 10) - -19315) + 6543);
			a135 = 34;
			a228 = a292;
			a339 = 0;
			a373 = 0;
			a234 = a372[1];
			a296 = a362;
			a240 = 0;
			a225 = a205[3];
			a235 = a216[4];
			a361 = 36;
			a368 = 0;
			a382 = ((((a382 + 23047) - 27584) % 12) - 43);
			a313 = 35;
			a134 = 1;
			a237 = 6;
			a206 = 11;
			a218 = 32;
			a230 = 5;
			a265 = a376;
			a196 = ((a172 - a172) + 15);
		} else {
			a368 = 0;
			a240 = 0;
			a269 = 32;
			a224 = 32;
			a260 = 0;
			a239 = a299;
			a211 = 4;
			a310 = ((((a310 * 5) - 18381) * -1) / 10);
			a373 = 0;
			a276 = a289;
			a155 = 35;
			a329 = 34;
			a218 = 36;
			a228 = a292;
			a75 = 33;
			a370 = a285;
			a339 = 0;
			a353 = a241;
			a132 = 0;
			a77 = (a172 - -2);
		}
	}
	if (((((152 < a249) && (355 >= a249)) && ((a172 == 5 && a269 == 32) && a105 == 33)) && (((103 == a276[1]) && (a207 == 32 && (((a173 == 34 && (cf == 1 && a75 == 32)) && a218 == 32) && input == inputs[0]))) && a225 == a205[1]))) {
		a122 -= (a122 - 20) < a122 ? 4 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if (((!(a338 == 9) || (a339 == 1 || a211 == 1)) && a307 == a227[4])) {
			a134 = 0;
			a196 = (a398 - -2);
			a75 = 35;
			a295 = a366[(a172 + -5)];
		} else {
			a359 = 9;
			a310 = (((((a310 + 386) + 24916) * 1) % 20) - -319);
			a336 = 0;
			a201 = (((56 / 5) - 23) - 56);
			a269 = 36;
			a211 = 3;
			a395 = 0;
			a286 = a294[2];
			a382 = ((((a382 - -27892) - 27735) - 25475) + 25496);
			a368 = 0;
			a353 = a399;
			a46 = a18;
			a338 = 6;
			a234 = a372[1];
			a202 = a217[7];
			a339 = 0;
			a329 = 34;
			a240 = 0;
			a370 = a311;
			a333 = (((52 + 5786) - 5819) * 5);
			a265 = a293;
			a260 = 0;
			a373 = 0;
			a224 = 36;
			a276 = a250;
			a392 = a257;
			a300 = 0;
			a207 = 32;
			a398 = 15;
			a313 = 32;
			a320 = 11;
			a270 = 15;
			a249 = ((((a249 + 16072) % 71) - -423) + 2);
			a357 = ((((a357 / 5) - 87) * 10) / 9);
			a237 = 7;
			a256 = 36;
			a235 = a216[1];
			a228 = a264;
			a386 = ((((a386 / 5) * 5) % 61) + 129);
			a206 = 5;
			a307 = a227[2];
			a324 = a232[6];
			a239 = a299;
			a146 = 1;
			a383 = a226[5];
			a358 = a348;
			a277 = (((66 + 6653) + 19131) - -2574);
			a218 = 36;
			a75 = 36;
			a13 = ((((31 + -2719) / 5) + 28608) + -27964);
		}
	}
	if ((((a206 == 5 && ((a313 == 32 && a218 == 32) && a260 != 1)) && a300 != 1) && (a75 == 32 && (a172 == 5 && ((((cf == 1 && a105 == 33) && a173 == 34) && a237 == 4) && input == inputs[9]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a295 = a366[((a172 * a237) - 15)];
		a75 = 35;
		a134 = 0;
		a53 = (((22 / 5) + -13468) + 17354);
	}
	if (((((input == inputs[1] && (a173 == 34 && (a105 == 33 && cf == 1))) && (28 == a370[0])) && a75 == 32) && (a218 == 32 && ((43 == a392[3]) && ((a172 == 5 && (a338 == 4 && a359 == 4)) && a211 == 2))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a174 += (a174 + 20) > a174 ? 4 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a132 = 0;
		a77 = a172;
		a75 = 33;
		a136 = ((a270 * a77) - 50);
	}
	if (((a336 != 1 && (a395 != 1 && (a105 == 33 && (a329 == 32 && (a270 == 11 && ((a172 == 5 && cf == 1) && input == inputs[6])))))) && (a173 == 34 && ((11 == a353[4]) && (a75 == 32 && (89 == a296[5])))))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a67 -= (a67 - 20) < a67 ? 1 : 0;
		a35 -= (a35 - 20) < a35 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a243 = ((((20 * 5) * 5) * 10) / -31);
		a256 = 33;
		a270 = 11;
		a382 = (((((a382 * 5) / 5) + 9319) % 12) - 60);
		a137 = a189;
		a277 = (((77 / 5) / 5) + -27457);
		a359 = 7;
		a386 = (((a386 - 26919) * 1) * 1);
		a240 = 0;
		a224 = 35;
		a296 = a384;
		a228 = a264;
		a368 = 0;
		a398 = 11;
		a336 = 0;
		a320 = 6;
		a218 = 36;
		a286 = a294[0];
		a302 = a346[1];
		a324 = a232[4];
		a333 = ((((85 - -13180) - 13284) * 10) / 9);
		a75 = 34;
		a237 = 6;
		a269 = 35;
		a57 = (a172 - -8);
		a235 = a216[3];
		a357 = (((((a357 % 65) + -105) * 5) % 65) + -66);
		a383 = a226[5];
		a230 = 3;
		a353 = a263;
		a260 = 0;
		a370 = a285;
		a339 = 1;
		a338 = 8;
		a201 = ((((80 + 15218) + -15386) * 10) / 9);
		a361 = 33;
		a300 = 0;
		a239 = a299;
		a395 = 0;
		a329 = 36;
		a225 = a205[5];
		a206 = 4;
		a358 = a351;
		a373 = 1;
		a265 = a293;
		a310 = (((a310 + 29371) - 16409) + 292);
		a211 = 2;
		a234 = a372[0];
		a312 = 35;
		a207 = 33;
		a307 = a227[7];
		a276 = a253;
		a154 = ((a57 * a57) + -159);
	}
}
void calculate_outputm73(int input) {
	if ((((a172 == 5 && (((a237 == 4 && a105 == 34) && a173 == 34) && a207 == 32)) && a260 != 1) && (a260 != 1 && ((a338 == 4 && ((cf == 1 && input == inputs[1]) && a75 == 32)) && (11 == a353[4]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a353 = a263;
		a302 = a346[0];
		a269 = 35;
		a265 = a303;
		a202 = a217[4];
		a243 = ((((99 + 27478) - -1223) * -1) / 10);
		a239 = a242;
		a307 = a227[0];
		a276 = a253;
		a339 = 0;
		a228 = a292;
		a312 = 32;
		a383 = a226[2];
		a234 = a372[5];
		a173 = 32;
		a224 = 36;
		a225 = a205[1];
		a81 = a167[((a211 * a172) - 8)];
		a382 = ((((24 * 74) / 10) + -26453) - -32952);
		a373 = 1;
		a329 = 35;
		a125 = a30[(a230 - -1)];
	}
	if (((((89 == a296[5]) && a237 == 4) && a173 == 34) && ((a172 == 5 && (a218 == 32 && (((((input == inputs[8] && cf == 1) && a105 == 34) && a312 == 32) && a75 == 32) && a230 == 4))) && ((-188 < a357) && (-57 >= a357))))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if (((!(60 == a197[4]) && (!(60 == a3[3]) || a339 == 1)) || !(20 == a137[1]))) {
			a173 = 36;
			a184 = a157[(a172 - 3)];
			a141 = a47[(a206 + -2)];
		} else {
			a336 = 0;
			a225 = a205[3];
			a202 = a217[6];
			a172 = (a359 + 3);
			a302 = a346[0];
			a276 = a289;
			a383 = a226[4];
			a239 = a268;
			a243 = ((((83 / 5) * -112) / 10) - 19987);
			a353 = a263;
			a307 = a227[4];
			a358 = a335;
			a329 = 36;
			a382 = (((73 * 5) / 5) + 9927);
			a99 = a26[(a172 - 5)];
		}
	}
	if (((a312 == 32 && ((a173 == 34 && cf == 1) && input == inputs[3])) && ((a75 == 32 && (((77 < a386) && (201 >= a386)) && ((a105 == 34 && ((a368 != 1 && a338 == 4) && a269 == 32)) && a172 == 5))) && ((-47 < a333) && (147 >= a333))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 2 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if ((a310 <= 160 && 307 < a36)) {
			a207 = 34;
			a320 = 8;
			a235 = a216[0];
			a358 = a351;
			a211 = 2;
			a224 = 34;
			a239 = a268;
			a310 = ((((a310 % 77) + 230) - 9683) - -9639);
			a333 = ((((a333 % 14) + 162) + 2) + -2);
			a243 = ((((64 + 29132) / 5) + -2912) - 3096);
			a201 = ((((a201 % 93) + -41) - 60) + -4);
			a370 = a285;
			a357 = (((((a357 - 1699) * 5) + -19791) % 65) + -57);
			a260 = 0;
			a339 = 0;
			a353 = a241;
			a312 = 34;
			a286 = a294[4];
			a237 = 8;
			a225 = a205[7];
			a234 = a372[1];
			a276 = a289;
			a378 = 0;
			a256 = 32;
			a307 = a227[4];
			a395 = 0;
			a338 = 10;
			a361 = 32;
			a77 = ((a230 + a270) + -6);
			a398 = 11;
			a75 = 33;
			a16 = 1;
			a230 = 5;
			a383 = a226[7];
			a218 = 32;
			a382 = ((((43 / 5) / 5) / 5) - -17999);
			a202 = a217[7];
			a206 = 11;
			a368 = 0;
			a313 = 32;
			a296 = a362;
			a249 = ((((81 * 5) + -18) * 10) / 9);
			a336 = 0;
			a386 = ((((((a386 % 61) - -112) + -7) * 5) % 61) + 103);
			a240 = 0;
			a359 = 7;
			a132 = 0;
			a269 = 34;
			a392 = a304;
			a277 = ((((a277 + 4639) * 10) / -9) - 23475);
			a329 = 36;
			a270 = 16;
		} else {
			a338 = 7;
			a240 = 0;
			a218 = 36;
			a270 = 10;
			a395 = 0;
			a105 = 36;
			a256 = 33;
			a158 = (a206 - -1);
			a75 = 34;
			a312 = 33;
			a225 = a205[1];
			a57 = ((a206 * a320) + -25);
			a207 = 33;
			a206 = 11;
			a357 = ((((a357 * 5) % 65) + -67) + -24);
			a313 = 33;
			a353 = a263;
			a224 = 36;
			a320 = 11;
		}
	}
	if (((a378 != 1 && (((-47 < a333) && (147 >= a333)) && (a218 == 32 && input == inputs[9]))) && ((a173 == 34 && ((76 == a358[5]) && ((a240 != 1 && (a75 == 32 && (cf == 1 && a105 == 34))) && a172 == 5))) && (43 == a392[3])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a169 -= (a169 - 20) < a169 ? 4 : 0;
		a35 -= (a35 - 20) < a35 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if ((((!(a177 == 34) && a54 <= 164) && a132 != 1) && a123 != 1)) {
			a336 = 0;
			a312 = 35;
			a173 = 35;
			a373 = 1;
			a329 = 33;
			a228 = a264;
			a302 = a346[6];
			a256 = 35;
			a383 = a226[2];
			a59 = 33;
			a368 = 0;
			a202 = a217[5];
			a353 = a263;
			a333 = (((a333 - -17140) - 22431) + 23164);
			a320 = 13;
			a386 = ((((a386 + -10390) / 5) * 10) / -9);
			a265 = a376;
			a358 = a348;
			a234 = a372[6];
			a249 = ((((94 + -27851) + -1179) * -1) / 10);
			a296 = a384;
			a91 = ((a359 * a230) + -9);
		} else {
			a77 = (a172 + 6);
			a307 = a227[5];
			a357 = (((a357 / 5) - -20905) * 1);
			a234 = a372[5];
			a239 = a268;
			a256 = 32;
			a313 = 35;
			a353 = a241;
			a358 = a351;
			a333 = (((a333 + -4412) * 5) - 1588);
			a338 = 6;
			a370 = a311;
			a260 = 0;
			a243 = (((((66 * 10) / -4) + -4) - 15499) + 15493);
			a300 = 0;
			a225 = a205[6];
			a324 = a232[1];
			a336 = 0;
			a240 = 0;
			a276 = a289;
			a99 = a26[(a172 + a211)];
			a368 = 0;
			a249 = ((((24 / 5) + 26329) * 10) / 9);
			a310 = ((((a310 % 77) - -186) - 11098) - -11091);
			a361 = 32;
			a202 = a217[6];
			a270 = 12;
			a230 = 10;
			a286 = a294[7];
			a386 = (((a386 + -9079) / 5) + 1940);
			a395 = 0;
			a237 = 5;
			a224 = 36;
			a75 = 33;
			a265 = a293;
			a378 = 0;
			a312 = 36;
			a359 = 9;
			a132 = 0;
			a269 = 34;
			a235 = a216[4];
			a206 = 8;
			a218 = 34;
			a296 = a212;
			a320 = 11;
			a339 = 1;
			a211 = 6;
		}
	}
	if (((((a286 == a294[1] && (((a173 == 34 && a256 == 32) && a234 == a372[1]) && a368 != 1)) && a105 == 34) && (28 == a370[0])) && (a75 == 32 && (a225 == a205[1] && ((cf == 1 && input == inputs[6]) && a172 == 5))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a178 += (a178 + 20) > a178 ? 3 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		if ((a123 != 1 && (a269 == 35 || (55 == a197[5])))) {
			a75 = 34;
			a141 = a47[((a398 * a270) - 119)];
			a57 = (a338 + 11);
			a72 = ((((((58 * -18) / 10) + 12121) / 5) * -1) / 10);
		} else {
			a57 = (a270 - -4);
			a75 = 34;
			a141 = a47[((a270 + a57) - 25)];
			a72 = (((87 - 15128) - -1435) * 2);
		}
	}
	if ((((((a269 == 32 && (a378 != 1 && (a173 == 34 && (cf == 1 && a172 == 5)))) && a105 == 34) && a260 != 1) && a361 == 32) && (((a75 == 32 && ((-199 < a201) && (-12 >= a201))) && input == inputs[5]) && a324 == a232[1]))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a67 -= (a67 - 20) < a67 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		if ((a206 == 5 && (a333 <= -47 || (31 == a137[0])))) {
			a302 = a346[2];
			a125 = a30[(a398 - 4)];
			a329 = 36;
			a202 = a217[0];
			a307 = a227[0];
			a243 = (((50 / 5) + 10770) / 5);
			a277 = (((a277 + -27876) + -402) / 5);
			a276 = a253;
			a382 = (((((40 + 16401) + -40966) / 5) * -1) / 10);
			a234 = a372[0];
			a353 = a241;
			a224 = 34;
			a173 = 32;
			a373 = 1;
			a239 = a268;
			a129 = a92[((a172 * a172) - 23)];
		} else {
			a240 = 0;
			a276 = a250;
			a378 = 0;
			a370 = a318;
			a211 = 5;
			a218 = 33;
			a324 = a232[1];
			a339 = 1;
			a333 = ((((a333 - 5876) / 5) * 10) / 9);
			a230 = 6;
			a57 = (a172 - -5);
			a395 = 0;
			a386 = ((((a386 * 5) / 5) % 61) + 81);
			a225 = a205[7];
			a353 = a241;
			a312 = 32;
			a336 = 0;
			a269 = 33;
			a270 = 13;
			a392 = a257;
			a300 = 0;
			a359 = 9;
			a358 = a348;
			a237 = 10;
			a75 = 34;
			a158 = (a398 + -7);
			a206 = 7;
			a277 = (((((a277 + -15131) * 1) + 1531) % 78) + 113);
			a234 = a372[3];
			a265 = a293;
			a373 = 1;
			a357 = (((a357 + 23090) / 5) * 5);
			a207 = 32;
			a296 = a212;
			a249 = ((((55 - 13111) * 2) - 2832) - -29258);
			a398 = 11;
			a338 = 4;
			a320 = 12;
			a313 = 32;
			a256 = 33;
			a228 = a264;
			a368 = 0;
			a361 = 36;
			a81 = a167[(a57 - 8)];
		}
	}
	if (((a206 == 5 && (((160 < a310) && (316 >= a310)) && (((a172 == 5 && ((cf == 1 && a75 == 32) && input == inputs[4])) && a320 == 7) && a368 != 1))) && (a105 == 34 && (a173 == 34 && (((-10 < a277) && (148 >= a277)) && a339 != 1))))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a269 = 36;
		a277 = (((((a277 + 18746) + 1964) / 5) * -1) / 10);
		a57 = ((a320 - a211) - -12);
		a357 = (((a357 / 5) - -5861) / 5);
		a75 = 34;
		a353 = a241;
		a218 = 33;
		a386 = (((((a386 % 61) - -103) - 24748) + 17440) - -7322);
		a40 = a83;
		a211 = 8;
		a320 = 13;
		a240 = 0;
		a333 = ((((a333 / 5) - -16733) + -34455) - -29145);
		a336 = 0;
		a378 = 0;
		a358 = a348;
		a265 = a303;
		a25 = a76;
	}
	if ((((((-10 < a277) && (148 >= a277)) && input == inputs[7]) && (28 == a370[0])) && ((a269 == 32 && ((((a173 == 34 && (a75 == 32 && (cf == 1 && a172 == 5))) && a105 == 34) && a237 == 4) && a395 != 1)) && a339 != 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 4 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if (((a221 == 1 && a277 <= -10) || a221 != 1)) {
			a139 = 35;
			a173 = 33;
			a130 = ((((35 / 5) + 25539) - -858) + -26061);
		} else {
			a143 = 35;
			a210 = 1;
			a75 = 34;
			a57 = ((a270 / a206) + 9);
		}
	}
	if (((a173 == 34 && (a218 == 32 && ((a313 == 32 && (((-10 < a277) && (148 >= a277)) && a224 == 32)) && input == inputs[0]))) && ((a172 == 5 && (a338 == 4 && ((cf == 1 && a105 == 34) && a75 == 32))) && a218 == 32))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a94 += (a94 + 20) > a94 ? 2 : 0;
		cf = 0;
		if ((414 < a17 && (a132 != 1 && a336 == 1))) {
			a44 = 32;
			a75 = 33;
			a132 = 0;
			a77 = (a398 - 3);
		} else {
			a146 = 1;
			a46 = a148;
			a75 = 36;
			a72 = (((39 - -27656) * 1) + 952);
		}
	}
	if (((a75 == 32 && ((input == inputs[2] && (a320 == 7 && (a270 == 11 && ((-10 < a277) && (148 >= a277))))) && a105 == 34)) && (((((cf == 1 && a173 == 34) && a172 == 5) && a313 == 32) && a256 == 32) && a218 == 32))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a94 += (a94 + 20) > a94 ? 3 : 0;
		cf = 0;
		a57 = (a338 + 6);
		a361 = 35;
		a269 = 34;
		a353 = a263;
		a211 = 6;
		a357 = (((((a357 / 5) - 24290) / 5) * -1) / 10);
		a270 = 11;
		a240 = 0;
		a398 = 16;
		a75 = 34;
		a202 = a217[3];
		a336 = 0;
		a370 = a311;
		a324 = a232[4];
		a312 = 32;
		a373 = 0;
		a339 = 1;
		a225 = a205[7];
		a243 = (((40 / 5) - 183) + 8);
		a256 = 32;
		a368 = 0;
		a313 = 36;
		a277 = (((a277 - 19458) - 10123) + 51819);
		a260 = 0;
		a239 = a299;
		a276 = a250;
		a358 = a351;
		a228 = a264;
		a230 = 6;
		a201 = ((((a201 * 5) % 94) - -149) + -27);
		a237 = 8;
		a158 = ((a57 - a172) + 1);
		a378 = 0;
		a296 = a212;
		a395 = 0;
		a207 = 33;
		a206 = 8;
		a333 = ((((a333 % 14) - -163) + 1) - 1);
		a235 = a216[2];
		a392 = a208;
		a386 = (((a386 / 5) / 5) + 311);
		a218 = 33;
		a320 = 7;
		a359 = 6;
		a310 = ((((((a310 % 77) - -206) + 1465) * 5) % 77) + 208);
		a338 = 3;
	}
}
void calculate_outputm76(int input) {
	if ((((a224 == 32 && (a202 == a217[1] && (a75 == 32 && ((103 == a276[1]) && a173 == 34)))) && a207 == 32) && (a368 != 1 && (a172 == 7 && (a230 == 4 && ((input == inputs[6] && cf == 1) && a99 == a26[1])))))) {
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		cf = 0;
		a202 = a217[(a270 - 11)];
		a373 = 1;
		a172 = (a320 - 6);
		a129 = a92[((a172 + a172) - 1)];
	}
}
void calculate_outputm77(int input) {
	if ((((a378 != 1 && (((152 < a249) && (355 >= a249)) && (a378 != 1 && ((160 < a310) && (316 >= a310))))) && a173 == 34) && ((a75 == 32 && ((((160 < a310) && (316 >= a310)) && ((a99 == a26[2] && cf == 1) && a172 == 7)) && a260 != 1)) && input == inputs[4]))) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a134 = 0;
		a296 = a362;
		a269 = 36;
		a218 = 32;
		a201 = ((((a201 * 5) % 94) + 137) + 27);
		a184 = a157[((a172 / a172) - -2)];
		a202 = a217[7];
		a359 = 6;
		a312 = 36;
		a207 = 36;
		a339 = 0;
		a333 = ((((a333 % 96) + 49) - 15076) - -15077);
		a224 = 34;
		a75 = 35;
		a310 = ((((a310 - 11383) * -1) / 10) * 5);
		a320 = 10;
		a378 = 0;
		a295 = a366[((a398 - a338) + -3)];
	}
	if (((((((77 < a386) && (201 >= a386)) && ((((cf == 1 && a99 == a26[2]) && a172 == 7) && a173 == 34) && a75 == 32)) && a383 == a226[1]) && (53 == a265[5])) && (((a395 != 1 && a235 == a216[1]) && input == inputs[2]) && (89 == a296[5])))) {
		a120 -= (a120 - 20) < a120 ? 2 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if ((((-199 < a201) && (-12 >= a201)) && a200 == 6)) {
			a211 = 4;
			a276 = a253;
			a172 = 1;
			a239 = a242;
			a225 = a205[7];
			a324 = a232[5];
			a307 = a227[5];
			a383 = a226[5];
			a353 = a263;
			a336 = 1;
			a234 = a372[7];
			a277 = (((((a277 + -13325) * -1) / 10) * 10) / 9);
			a202 = a217[5];
			a129 = a92[(a172 / a172)];
		} else {
			a225 = a205[0];
			a249 = (((((a249 * 5) * 10) / 9) / 5) + 24344);
			a307 = a227[4];
			a201 = (((a201 - 20548) - -49572) - 28836);
			a398 = 12;
			a353 = a399;
			a256 = 35;
			a300 = 1;
			a361 = 35;
			a173 = 33;
			a191 = a37[(a172 + -1)];
			a202 = a217[6];
			a358 = a335;
			a228 = a292;
			a333 = (((((a333 % 14) - -162) + -1) + 16612) - 16609);
			a265 = a303;
			a336 = 0;
			a329 = 36;
			a130 = (((38 / -5) * 5) / 5);
		}
	}
	if ((((a269 == 32 && (((a172 == 7 && (cf == 1 && a75 == 32)) && a269 == 32) && ((-179 < a243) && (-156 >= a243)))) && input == inputs[1]) && (a99 == a26[2] && (a173 == 34 && ((a339 != 1 && (40 == a239[3])) && ((-199 < a201) && (-12 >= a201))))))) {
		a174 += (a174 + 20) > a174 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		if ((!(3 == a353[2]) || (!(a139 == 32) && ((!(a324 == 8) && 121 < a170) && !(5 == a25[0]))))) {
			a57 = (a172 + 9);
			a75 = 34;
			a278 = a326[((a211 * a320) - 14)];
			a19 = (((((36 / 5) * 439) / 10) / 5) - -272);
		} else {
			a313 = 34;
			a260 = 1;
			a235 = a216[2];
			a339 = 0;
			a333 = ((((a333 / 5) % 14) - -162) + 1);
			a383 = a226[0];
			a386 = (((a386 - 2691) - 19378) / 5);
			a373 = 1;
			a296 = a362;
			a134 = 0;
			a329 = 35;
			a361 = 35;
			a357 = (((((a357 + -26727) % 38) + 9) - 13781) + 13783);
			a353 = a399;
			a211 = 3;
			a312 = 36;
			a392 = a208;
			a378 = 0;
			a201 = (((a201 - 17744) - 9967) * 1);
			a269 = 36;
			a307 = a227[6];
			a237 = 9;
			a359 = 6;
			a277 = (((a277 + 169) - 567) - -560);
			a302 = a346[0];
			a395 = 0;
			a224 = 36;
			a398 = 14;
			a234 = a372[4];
			a206 = 7;
			a320 = 13;
			a300 = 0;
			a202 = a217[3];
			a270 = 17;
			a295 = a366[(a338 + -2)];
			a239 = a299;
			a75 = 35;
			a265 = a293;
			a218 = 34;
			a249 = ((((a249 * 10) / 3) / 5) + 27819);
			a207 = 34;
			a368 = 1;
			a286 = a294[7];
			a230 = 10;
			a370 = a311;
			a324 = a232[2];
			a310 = ((((a310 % 20) - -335) + 27625) - 27627);
			a382 = ((((a382 - 8270) - -35983) * -1) / 10);
			a256 = 32;
			a240 = 1;
			a171 = 36;
			a243 = ((((a243 / 5) / 5) * 9) / 10);
			a225 = a205[5];
			a338 = 7;
		}
	}
	if (((a237 == 4 && (a359 == 4 && (((a339 != 1 && ((-199 < a201) && (-12 >= a201))) && (43 == a392[3])) && a172 == 7))) && ((a173 == 34 && (((a75 == 32 && cf == 1) && a99 == a26[2]) && ((-199 < a201) && (-12 >= a201)))) && input == inputs[3]))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a174 += (a174 + 20) > a174 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		cf = 0;
		a234 = a372[1];
		a225 = a205[4];
		a265 = a293;
		a398 = 13;
		a368 = 0;
		a370 = a318;
		a269 = 36;
		a235 = a216[1];
		a320 = 12;
		a237 = 3;
		a361 = 36;
		a207 = 36;
		a373 = 1;
		a395 = 0;
		a201 = ((((a201 * 5) % 93) - 14) + 2);
		a211 = 4;
		a206 = 10;
		a260 = 0;
		a386 = (((a386 - 27105) + -2525) - -54634);
		a336 = 0;
		a239 = a299;
		a137 = a189;
		a357 = (((a357 - -24262) - -4838) - -476);
		a270 = 15;
		a75 = 34;
		a300 = 0;
		a277 = (((((a277 % 78) - -70) - 2) + -10515) - -10515);
		a310 = (((a310 * 5) - 3196) / 5);
		a243 = (((a243 - 7493) - -15513) * 3);
		a338 = 9;
		a228 = a229;
		a382 = (((a382 + 29703) * 1) - -233);
		a312 = 32;
		a296 = a212;
		a256 = 36;
		a329 = 36;
		a307 = a227[0];
		a154 = (a230 - -6);
		a286 = a294[5];
		a202 = a217[3];
		a240 = 0;
		a276 = a289;
		a339 = 1;
		a324 = a232[1];
		a333 = (((a333 + 22856) * 1) - 24949);
		a218 = 36;
		a358 = a351;
		a224 = 32;
		a302 = a346[7];
		a359 = 3;
		a57 = (a230 + 9);
		a230 = 10;
	}
	if (((input == inputs[9] && ((((-188 < a357) && (-57 >= a357)) && a324 == a232[1]) && a172 == 7)) && (a398 == 11 && (a320 == 7 && (a224 == 32 && (a260 != 1 && (a75 == 32 && ((a99 == a26[2] && cf == 1) && a173 == 34)))))))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a169 -= (a169 - 20) < a169 ? 4 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		cf = 0;
		a75 = 36;
		a146 = 0;
		a73 = (((65 / 5) - 19868) - 4330);
		a39 = a152;
	}
	if (((((a224 == 32 && (((a173 == 34 && (cf == 1 && a99 == a26[2])) && a378 != 1) && a312 == 32)) && a172 == 7) && a75 == 32) && (((-65 < a382) && (-39 >= a382)) && (a207 == 32 && (a207 == 32 && input == inputs[5]))))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a162 -= (a162 - 20) < a162 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		cf = 0;
		if (a130 <= 134) {
			a172 = ((a206 - a206) + 1);
			a129 = a92[((a230 / a172) - 1)];
		} else {
			a132 = 0;
			a77 = (a172 + 3);
			a75 = 33;
			a1 = a87[(a77 - 8)];
		}
	}
	if (((a256 == 32 && (((-47 < a333) && (147 >= a333)) && (((a172 == 7 && a230 == 4) && a173 == 34) && a211 == 2))) && (a312 == 32 && ((a75 == 32 && (input == inputs[6] && (a99 == a26[2] && cf == 1))) && a211 == 2)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if ((!(a191 == a37[2]) && (((a234 == 11 || a324 == a232[6]) && a132 != 1) && !(a295 == 13)))) {
			a75 = 33;
			a44 = 32;
			a132 = 0;
			a77 = (a398 + -3);
		} else {
			a173 = 35;
			a228 = a229;
			a202 = a217[3];
			a91 = (a230 - -4);
			a361 = 32;
			a312 = 36;
			a296 = a384;
			a265 = a303;
			a276 = a253;
			a239 = a299;
			a353 = a399;
			a225 = a205[4];
			a277 = (((((a277 * 5) - -19723) - 35236) * -1) / 10);
			a358 = a335;
			a373 = 1;
			a324 = a232[5];
			a307 = a227[5];
			a333 = (((a333 / 5) - 20) + 22);
			a336 = 1;
			a102 = a127[((a206 + a91) - 8)];
		}
	}
	if (((((a395 != 1 && a173 == 34) && a235 == a216[1]) && a269 == 32) && (((input == inputs[7] && (a256 == 32 && (((a172 == 7 && cf == 1) && a75 == 32) && a99 == a26[2]))) && a234 == a372[1]) && (43 == a392[3])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a169 -= (a169 - 20) < a169 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a225 = a205[4];
		a296 = a362;
		a269 = 34;
		a237 = 5;
		a339 = 0;
		a313 = 36;
		a218 = 34;
		a338 = 10;
		a310 = (((a310 / 5) + 247) - -4);
		a249 = (((a249 - -28201) - -1332) * 1);
		a333 = (((a333 + 28109) - -354) * 1);
		a206 = 7;
		a359 = 6;
		a370 = a285;
		a201 = ((((a201 + 3041) - -26239) % 93) + -152);
		a398 = 15;
		a307 = a227[4];
		a320 = 12;
		a383 = a226[2];
		a75 = 35;
		a134 = 0;
		a224 = 36;
		a295 = a366[(a172 - 3)];
		a357 = ((((a357 * 5) * 10) / -9) / 5);
		a240 = 0;
		a312 = 35;
		a202 = a217[3];
		a256 = 32;
		a239 = a299;
		a260 = 0;
		a184 = a157[a172];
	}
	if (((((((-10 < a277) && (148 >= a277)) && (a300 != 1 && ((cf == 1 && a173 == 34) && a172 == 7))) && a75 == 32) && input == inputs[8]) && ((a324 == a232[1] && (a99 == a26[2] && (a361 == 32 && a398 == 11))) && a361 == 32))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a5 -= (a5 - 20) < a5 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a329 = 35;
		a206 = 6;
		a307 = a227[1];
		a154 = (a172 - -8);
		a333 = ((((a333 + -13429) - -18367) * 10) / -9);
		a256 = 32;
		a320 = 13;
		a269 = 36;
		a361 = 36;
		a359 = 8;
		a312 = 36;
		a382 = (((((a382 % 12) - 43) * 10) / 9) - 3);
		a338 = 7;
		a234 = a372[3];
		a276 = a253;
		a240 = 0;
		a368 = 0;
		a228 = a229;
		a336 = 0;
		a239 = a299;
		a57 = (a237 - -9);
		a211 = 4;
		a386 = (((a386 / -5) - -28877) / -5);
		a235 = a216[7];
		a357 = ((((((a357 % 65) + -63) + -46) * 5) % 65) - 99);
		a75 = 34;
		a218 = 36;
		a296 = a384;
		a300 = 0;
		a313 = 34;
		a249 = ((((a249 * 5) * 5) - 13903) - -32825);
		a339 = 1;
		a137 = a189;
		a324 = a232[5];
		a265 = a376;
		a237 = 10;
	}
	if (((a172 == 7 && (input == inputs[0] && (28 == a370[0]))) && ((a173 == 34 && (((a320 == 7 && (((a75 == 32 && cf == 1) && a99 == a26[2]) && a329 == 32)) && a383 == a226[1]) && ((-47 < a333) && (147 >= a333)))) && a206 == 5))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a333 = ((((a333 + -11249) - 12864) * 10) / 9);
		a300 = 0;
		a201 = (((a201 / 5) + -34) + 8);
		a357 = (((a357 * 5) + 997) * 5);
		a240 = 0;
		a243 = ((((a243 + -26870) - -8504) % 11) + -162);
		a234 = a372[6];
		a368 = 0;
		a265 = a303;
		a358 = a335;
		a382 = (((a382 / 5) / 5) + -1971);
		a276 = a253;
		a277 = (((a277 - -28711) - 57611) + -267);
		a392 = a257;
		a57 = (a172 + 5);
		a211 = 4;
		a378 = 0;
		a383 = a226[5];
		a206 = 4;
		a302 = a346[5];
		a329 = 33;
		a256 = 32;
		a310 = (((a310 * 5) + 11669) / 5);
		a224 = 36;
		a286 = a294[1];
		a237 = 9;
		a395 = 0;
		a296 = a212;
		a270 = 13;
		a336 = 0;
		a398 = 16;
		a235 = a216[7];
		a307 = a227[3];
		a359 = 9;
		a320 = 12;
		a269 = 32;
		a228 = a264;
		a81 = a167[(a57 - 10)];
		a370 = a318;
		a338 = 9;
		a312 = 36;
		a239 = a242;
		a324 = a232[1];
		a75 = 34;
		a386 = (((((a386 * 5) + -3419) - 6339) * -1) / 10);
		a202 = a217[3];
		a207 = 36;
		a249 = ((((a249 * 5) * 5) * 10) / 9);
		a218 = 35;
		a230 = 6;
		a225 = a205[0];
		a339 = 1;
		a373 = 1;
		a158 = (a172 - -4);
	}
}
void calculate_outputm78(int input) {
	if (((a302 == a346[1] && (a211 == 2 && ((input == inputs[1] && (a75 == 32 && a224 == 32)) && a256 == 32))) && (a224 == 32 && (a173 == 34 && ((76 == a358[5]) && (a172 == 7 && (cf == 1 && a99 == a26[5]))))))) {
		a161 -= (a161 - 20) < a161 ? 2 : 0;
		cf = 0;
		a172 = (a320 - 3);
		a274 = a290;
	}
	if (((a75 == 32 && (53 == a265[5])) && (a237 == 4 && ((a398 == 11 && (((((-10 < a277) && (148 >= a277)) && ((input == inputs[9] && (cf == 1 && a173 == 34)) && a172 == 7)) && a99 == a26[5]) && ((77 < a386) && (201 >= a386)))) && a260 != 1)))) {
		cf = 0;
		if ((a141 == a47[4] || !(a143 == 34))) {
			a302 = a346[(a320 + -5)];
			a173 = 32;
			a218 = 34;
			a383 = a226[((a206 + a398) - 14)];
			a353 = a399;
			a129 = a92[((a172 / a270) - -7)];
			a358 = a335;
			a398 = (a359 - -8);
			a333 = ((((((a333 * a310) % 14999) % 14) - -162) + -1) - 0);
			a125 = a30[(a359 + 3)];
			a368 = 1;
			a256 = 34;
			a202 = a217[(a320 + -5)];
		} else {
			a373 = 1;
			a329 = 33;
			a312 = 33;
			a358 = a348;
			a310 = (((((a357 * a243) % 14999) - 27594) - 2247) - -1946);
			a361 = 33;
			a295 = a366[((a230 / a237) - 1)];
			a201 = (((((((a310 * a277) % 14999) * 2) - 1) * 1) % 14900) - 15098);
			a256 = 34;
			a320 = (a398 + -5);
			a196 = ((a359 / a206) - -17);
			a359 = (a320 - 3);
			a336 = 1;
			a260 = 1;
			a383 = a226[((a211 * a398) + -20)];
			a338 = ((a398 * a398) - 118);
			a202 = a217[(a211 / a398)];
			a134 = 0;
			a228 = a229;
			a302 = a346[(a398 - 11)];
			a357 = ((((((a357 * a310) % 14999) / 5) % 38) + -17) + -1);
			a224 = 33;
			a207 = 33;
			a353 = a263;
			a230 = ((a398 * a398) - 118);
			a300 = 1;
			a370 = a318;
			a392 = a208;
			a368 = 1;
			a269 = 33;
			a382 = ((((a243 * a277) - 3503) + -86) - 51);
			a324 = a232[(a338 - 1)];
			a75 = 35;
			a276 = a253;
			a240 = 1;
			a237 = (a398 + -6);
			a225 = a205[(a172 - 7)];
			a333 = (((((a333 * a386) + 27) % 14976) - 15022) + -3);
			a395 = 1;
			a277 = ((((((a310 * a310) % 14999) - 11180) % 95) - -243) * 1);
			a265 = a303;
			a398 = (a211 + 10);
			a211 = ((a270 - a270) - -3);
			a218 = 33;
			a339 = 1;
			a234 = a372[(a320 / a270)];
		}
	}
}
void calculate_outputm79(int input) {
	if (((a313 == 32 && ((a368 != 1 && (a172 == 7 && (a173 == 34 && ((a75 == 32 && cf == 1) && input == inputs[2])))) && a378 != 1)) && (((a395 != 1 && (76 == a358[5])) && a99 == a26[6]) && a240 != 1))) {
		cf = 0;
		a224 = 33;
		a225 = a205[(a359 - 4)];
		a361 = 32;
		a234 = a372[(a398 - 9)];
		a125 = a30[(a172 - a172)];
		a173 = 32;
		a277 = ((((((a277 * a382) % 95) + 244) + 1) - -28385) - 28386);
		a383 = a226[(a338 - 4)];
		a54 = ((((35 / 5) + 18222) * 10) / 9);
	}
}
void calculate_outputm5(int input) {
	if (((a395 != 1 && (a256 == 32 && a286 == a294[1])) && (((((77 < a386) && (201 >= a386)) && (cf == 1 && a172 == 1)) && ((152 < a249) && (355 >= a249))) && a320 == 7))) {
		if (((a270 == 11 && (((-65 < a382) && (-39 >= a382)) && ((-179 < a243) && (-156 >= a243)))) && (a270 == 11 && (a224 == 32 && (a235 == a216[1] && (cf == 1 && a129 == a92[1])))))) {
			calculate_outputm65(input);
		}
		if (((((89 == a296[5]) && ((a361 == 32 && a336 != 1) && a320 == 7)) && a206 == 5) && (a336 != 1 && (cf == 1 && a129 == a92[2])))) {
			calculate_outputm66(input);
		}
		if (((a129 == a92[7] && cf == 1) && (a329 == 32 && (((89 == a296[5]) && ((103 == a276[1]) && (((152 < a249) && (355 >= a249)) && a324 == a232[1]))) && ((-47 < a333) && (147 >= a333)))))) {
			calculate_outputm68(input);
		}
	}
	if (((a269 == 32 && a260 != 1) && ((((53 == a265[5]) && ((a172 == 5 && cf == 1) && (28 == a370[0]))) && a336 != 1) && a361 == 32))) {
		if (((a206 == 5 && ((50 == a228[0]) && ((28 == a370[0]) && a270 == 11))) && (((a105 == 33 && cf == 1) && (40 == a239[3])) && a207 == 32))) {
			calculate_outputm72(input);
		}
		if (((a324 == a232[1] && ((a286 == a294[1] && (((a105 == 34 && cf == 1) && ((160 < a310) && (316 >= a310))) && a359 == 4)) && a320 == 7)) && a300 != 1)) {
			calculate_outputm73(input);
		}
	}
	if (((a398 == 11 && a359 == 4) && (a378 != 1 && ((a361 == 32 && ((cf == 1 && a172 == 7) && a202 == a217[1])) && ((-47 < a333) && (147 >= a333)))))) {
		if ((((103 == a276[1]) && (a302 == a346[1] && (((a99 == a26[1] && cf == 1) && a270 == 11) && a359 == 4))) && (a398 == 11 && a373 != 1))) {
			calculate_outputm76(input);
		}
		if (((a383 == a226[1] && (((cf == 1 && a99 == a26[2]) && ((152 < a249) && (355 >= a249))) && (43 == a392[3]))) && ((a260 != 1 && a207 == 32) && a260 != 1))) {
			calculate_outputm77(input);
		}
		if (((((-179 < a243) && (-156 >= a243)) && ((cf == 1 && a99 == a26[5]) && a383 == a226[1])) && (((a302 == a346[1] && a312 == 32) && ((-47 < a333) && (147 >= a333))) && (11 == a353[4])))) {
			calculate_outputm78(input);
		}
		if ((((((((-10 < a277) && (148 >= a277)) && a339 != 1) && a395 != 1) && (43 == a392[3])) && a359 == 4) && ((cf == 1 && a99 == a26[6]) && a234 == a372[1]))) {
			calculate_outputm79(input);
		}
	}
}
void calculate_outputm81(int input) {
	if (((a173 == 35 && (((cf == 1 && input == inputs[8]) && a75 == 32) && a230 == 4)) && ((((a91 == 7 && (a59 == 33 && (a359 == 4 && a240 != 1))) && a373 != 1) && a383 == a226[1]) && a395 != 1))) {
		a5 -= (a5 - 20) < a5 ? 1 : 0;
		cf = 0;
		a173 = 33;
		a225 = a205[(a230 - 4)];
		a357 = (((((((a333 * a333) % 14999) + -28967) / 5) - 7297) % 38) - -13);
		a265 = a376;
		a313 = 33;
		a211 = (a206 + -4);
		a378 = 1;
		a260 = 1;
		a218 = 34;
		a276 = a253;
		a206 = a230;
		a320 = (a237 + a237);
		a201 = ((((((a201 * a357) / 5) % 94) + 84) + -23012) + 23011);
		a368 = 1;
		a143 = 34;
		a339 = 1;
		a361 = 34;
		a373 = 0;
		a359 = ((a230 - a230) + 3);
		a312 = 33;
		a338 = ((a91 * a320) - 53);
		a398 = (a237 + 8);
		a324 = a232[(a270 + -9)];
		a228 = a229;
		a235 = a216[((a320 - a91) - 1)];
		a75 = 34;
		a296 = a212;
		a57 = ((a237 - a270) - -18);
		a270 = (a237 + 8);
		a300 = 1;
		a230 = (a398 + -7);
		a234 = a372[(a237 + -2)];
		a240 = 1;
		a237 = 3;
	}
	if (((a225 == a205[1] && ((a75 == 32 && (a300 != 1 && a173 == 35)) && a260 != 1)) && (a329 == 32 && (a378 != 1 && (a91 == 7 && ((input == inputs[4] && (cf == 1 && a59 == 33)) && a302 == a346[1])))))) {
		a169 -= (a169 - 20) < a169 ? 2 : 0;
		cf = 0;
		a57 = ((a91 * a91) + -36);
		a329 = 34;
		a324 = a232[((a91 + a91) + -12)];
		a137 = a189;
		a269 = 34;
		a339 = 0;
		a313 = 33;
		a373 = 1;
		a154 = ((a57 * a206) + -50);
		a235 = a216[(a359 - 4)];
		a225 = a205[((a206 + a211) + -7)];
		a75 = 34;
		a357 = ((((((a357 * a310) % 14999) % 38) + -17) + -2) - 0);
		a218 = 34;
		a211 = (a230 + -1);
		a338 = a206;
		a240 = 1;
		a361 = 33;
		a359 = (a237 + 1);
		a206 = ((a237 * a91) - 24);
		a300 = 1;
		a237 = (a57 + -10);
	}
}
void calculate_outputm82(int input) {
	if (((((a234 == a372[1] && a286 == a294[1]) && a91 == 8) && input == inputs[1]) && (a237 == 4 && (((50 == a228[0]) && (((11 == a353[4]) && ((cf == 1 && a173 == 35) && a102 == a127[5])) && a75 == 32)) && a224 == 32)))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a98 += (a98 + 20) > a98 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a75 = 34;
		a71 = a175[(a91 - 4)];
		a134 = 0;
		a57 = ((a359 / a398) - -14);
	}
	if (((((a329 == 32 && a256 == 32) && ((160 < a310) && (316 >= a310))) && a269 == 32) && (a286 == a294[1] && (((((a75 == 32 && (a102 == a127[5] && cf == 1)) && a91 == 8) && a173 == 35) && input == inputs[9]) && (76 == a358[5]))))) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		if ((cf == 1 || !(a206 == 7))) {
			a378 = 0;
			a373 = 1;
			a173 = 32;
			a239 = a242;
			a276 = a253;
			a336 = 0;
			a265 = a303;
			a329 = 35;
			a312 = 33;
			a324 = a232[4];
			a361 = 36;
			a333 = ((((54 + -9226) - -9324) - -5090) + -5087);
			a202 = a217[4];
			a277 = (((((36 * 5) * 10) / 5) - 28137) + 56674);
			a107 = 33;
			a125 = a30[(a230 + 2)];
		} else {
			a136 = (a270 + -6);
			a75 = 33;
			a132 = 0;
			a77 = (a237 + 1);
		}
	}
	if (((((-65 < a382) && (-39 >= a382)) && (input == inputs[3] && (cf == 1 && a102 == a127[5]))) && ((43 == a392[3]) && (((((a234 == a372[1] && ((43 == a392[3]) && a234 == a372[1])) && (76 == a358[5])) && a91 == 8) && a173 == 35) && a75 == 32)))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a5 -= (a5 - 20) < a5 ? 4 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		if ((a59 == 32 || (a333 <= -47 || a81 == a167[5]))) {
			a196 = (a320 - -5);
			a134 = 1;
			a75 = 35;
			a54 = (((54 - 25552) * 1) * 1);
		} else {
			a75 = 35;
			a134 = 0;
			a295 = a366[(a338 - 1)];
			a170 = ((((52 / 5) * -5) + 26377) + -45037);
		}
	}
	if (((((77 < a386) && (201 >= a386)) && ((((a102 == a127[5] && ((a91 == 8 && (cf == 1 && a75 == 32)) && (11 == a353[4]))) && input == inputs[8]) && a286 == a294[1]) && a307 == a227[1])) && ((((-199 < a201) && (-12 >= a201)) && (28 == a370[0])) && a173 == 35))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		a161 -= (a161 - 20) < a161 ? 3 : 0;
		cf = 0;
		a129 = a92[((a211 * a91) + -16)];
		a134 = 1;
		a75 = 35;
		a196 = (a230 - -6);
	}
	if (((a383 == a226[1] && ((input == inputs[0] && (((a173 == 35 && (cf == 1 && a102 == a127[5])) && a211 == 2) && a75 == 32)) && a329 == 32)) && (((a91 == 8 && a286 == a294[1]) && a269 == 32) && a339 != 1))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a169 -= (a169 - 20) < a169 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		if ((!(92 == a296[2]) || (a206 == 8 && (a130 <= 134 || a191 == a37[4])))) {
			a132 = 0;
			a129 = a92[(a320 - 4)];
			a75 = 33;
			a77 = (a398 + 1);
		} else {
			a75 = 34;
			a81 = a167[((a270 + a359) + -10)];
			a57 = (a91 + 4);
			a170 = ((((41 + 5947) + -5953) / 5) - -55);
		}
	}
	if ((((a300 != 1 && ((a75 == 32 && (a173 == 35 && (a102 == a127[5] && (input == inputs[2] && (cf == 1 && a91 == 8))))) && a336 != 1)) && a225 == a205[1]) && ((a383 == a226[1] && a260 != 1) && a256 == 32))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		a94 += (a94 + 20) > a94 ? 1 : 0;
		cf = 0;
		if ((a286 == 4 && !(a107 == 32))) {
			a368 = 0;
			a237 = 7;
			a134 = 0;
			a202 = a217[2];
			a277 = ((((92 * 37) / 10) - -15356) * 1);
			a235 = a216[5];
			a382 = ((((((a382 % 12) - 39) + -8) * 5) % 12) - 48);
			a230 = 8;
			a386 = ((((a386 % 61) - -202) / 5) - -195);
			a269 = 32;
			a224 = 35;
			a378 = 0;
			a276 = a289;
			a338 = 8;
			a392 = a304;
			a359 = 5;
			a75 = 35;
			a302 = a346[6];
			a336 = 0;
			a171 = 32;
			a353 = a241;
			a265 = a376;
			a207 = 36;
			a307 = a227[3];
			a211 = 8;
			a339 = 0;
			a228 = a292;
			a333 = ((((80 - -27644) + -27571) * 10) / 9);
			a358 = a335;
			a320 = 13;
			a329 = 35;
			a239 = a299;
			a234 = a372[3];
			a225 = a205[7];
			a218 = 35;
			a240 = 0;
			a270 = 16;
			a313 = 32;
			a201 = ((((((a201 - -17933) % 93) - 125) * 5) % 93) - 68);
			a206 = 10;
			a300 = 0;
			a357 = ((((((a357 % 65) - 87) * 10) / 9) - 27093) + 27082);
			a398 = 15;
			a243 = (((a243 / 5) / 5) - -27890);
			a249 = ((((a249 / 5) * -5) - -21815) + -30910);
			a295 = a366[(a91 - 6)];
		} else {
			a57 = (a230 - -13);
			a75 = 34;
			a40 = a83;
			a25 = a68;
		}
	}
	if (((((77 < a386) && (201 >= a386)) && (((a173 == 35 && a269 == 32) && a91 == 8) && a307 == a227[1])) && (((160 < a310) && (316 >= a310)) && ((((a75 == 32 && (a102 == a127[5] && cf == 1)) && input == inputs[5]) && (76 == a358[5])) && ((160 < a310) && (316 >= a310)))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a162 -= (a162 - 20) < a162 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		if ((!(a99 == a26[3]) && a237 == 6)) {
			a353 = a241;
			a357 = ((((a357 % 65) + -108) + 40) + 7);
			a269 = 33;
			a57 = ((a270 + a359) + 2);
			a382 = ((((((a382 % 12) + -41) + -6) / 5) * 49) / 10);
			a211 = 7;
			a218 = 33;
			a40 = a83;
			a386 = (((((a386 - 7262) % 61) - -162) - -21898) - 21878);
			a336 = 0;
			a307 = a227[1];
			a302 = a346[6];
			a320 = 13;
			a358 = a348;
			a378 = 0;
			a75 = 34;
			a240 = 0;
			a25 = a76;
		} else {
			a139 = 33;
			a173 = 33;
			a130 = (((9 - 24174) * 1) + 24580);
		}
	}
	if ((((((((input == inputs[7] && (a102 == a127[5] && cf == 1)) && a378 != 1) && ((160 < a310) && (316 >= a310))) && a173 == 35) && a237 == 4) && a269 == 32) && (((50 == a228[0]) && ((43 == a392[3]) && a91 == 8)) && a75 == 32))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a359 = 9;
		a382 = (((a382 / 5) + 4152) + 10014);
		a201 = (((a201 + 28572) * 1) + -25774);
		a336 = 1;
		a358 = a335;
		a276 = a253;
		a207 = 36;
		a142 = 0;
		a370 = a318;
		a307 = a227[4];
		a91 = ((a206 / a338) - -11);
		a235 = a216[7];
		a239 = a242;
		a329 = 34;
		a312 = 33;
		a277 = ((((82 * 5) - 387) + 5579) + -5519);
		a324 = a232[0];
		a333 = ((((((26 * 69) / 10) * 5) - 6712) * -1) / 10);
		a339 = 1;
		a286 = a294[3];
		a202 = a217[3];
		a398 = 15;
		a302 = a346[5];
		a260 = 1;
		a373 = 1;
		a265 = a303;
		a296 = a362;
		a243 = (((((a243 / -5) * 10) / 9) * 10) / 9);
		a230 = 3;
		a228 = a264;
		a353 = a263;
		a206 = 4;
	}
	if ((((a395 != 1 && ((input == inputs[4] && (a173 == 35 && ((a75 == 32 && cf == 1) && a102 == a127[5]))) && a237 == 4)) && ((152 < a249) && (355 >= a249))) && ((((152 < a249) && (355 >= a249)) && (a368 != 1 && a359 == 4)) && a91 == 8))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a35 -= (a35 - 20) < a35 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		a57 = ((a91 + a91) + -1);
		a75 = 34;
		a72 = ((((((a243 * a243) % 14999) % 101) + -9) - -8) / 5);
		a36 = ((((((a72 * a72) % 14) + 292) * 5) % 14) + 293);
	}
	if ((((a336 != 1 && ((a338 == 4 && (a173 == 35 && (((cf == 1 && a102 == a127[5]) && a75 == 32) && a91 == 8))) && a286 == a294[1])) && a368 != 1) && (input == inputs[6] && (a383 == a226[1] && a207 == 32)))) {
		a120 -= (a120 - 20) < a120 ? 4 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		if ((!(a234 == 9) && (a323 == 8 && (!(a398 == 13) && a323 == 10)))) {
			a228 = a264;
			a320 = 13;
			a218 = 35;
			a158 = ((a338 + a398) + -10);
			a307 = a227[5];
			a276 = a289;
			a237 = 3;
			a224 = 32;
			a324 = a232[3];
			a310 = (((a310 - -15663) / 5) + 17785);
			a392 = a257;
			a265 = a376;
			a230 = 10;
			a225 = a205[7];
			a313 = 32;
			a57 = (a211 + 8);
			a249 = ((((a249 / 5) + -2617) * 10) / 9);
			a329 = 36;
			a357 = ((((a357 - -18367) * 10) / 9) * 1);
			a200 = a115[((a206 + a158) + -8)];
			a368 = 0;
			a370 = a318;
			a240 = 0;
			a378 = 0;
			a201 = ((((a201 % 93) - 23) - -29514) + -29586);
			a75 = 34;
			a256 = 33;
			a353 = a241;
			a206 = 8;
			a270 = 16;
			a243 = (((((a243 * 10) / 8) / 5) * 46) / 10);
			a395 = 0;
			a211 = 2;
			a207 = 36;
			a234 = a372[1];
			a302 = a346[3];
			a383 = a226[0];
			a338 = 10;
			a358 = a348;
			a359 = 9;
			a339 = 1;
			a382 = (((a382 + -9241) - -20470) + 587);
			a336 = 0;
			a235 = a216[3];
			a269 = 32;
			a312 = 32;
			a286 = a294[4];
			a300 = 0;
			a398 = 13;
		} else {
			a57 = (a91 + 5);
			a358 = a351;
			a370 = a285;
			a237 = 10;
			a302 = a346[3];
			a329 = 33;
			a307 = a227[1];
			a234 = a372[1];
			a398 = 13;
			a75 = 34;
			a383 = a226[6];
			a269 = 33;
			a353 = a263;
			a320 = 11;
			a395 = 0;
			a368 = 0;
			a339 = 1;
			a224 = 33;
			a225 = a205[1];
			a382 = (((a382 + 5870) / 5) + -1218);
			a300 = 1;
			a357 = ((((a357 * 10) / -9) + 19942) - -4815);
			a207 = 32;
			a392 = a257;
			a228 = a264;
			a359 = 10;
			a386 = ((((a386 / 5) + 116) * 9) / 10);
			a312 = 32;
			a243 = ((((a243 - 26456) * 10) / 9) + -255);
			a230 = 8;
			a286 = a294[7];
			a260 = 0;
			a256 = 33;
			a277 = ((((7 - -11700) * 10) / -9) - -8132);
			a218 = 35;
			a154 = (a91 - -8);
			a211 = 7;
			a338 = 8;
			a336 = 0;
			a313 = 33;
			a235 = a216[5];
			a270 = 16;
			a240 = 0;
			a249 = (((a249 / 5) - -12867) * -2);
			a206 = 7;
			a324 = a232[5];
			a137 = a189;
		}
	}
}
void calculate_outputm83(int input) {
	if (((a207 == 32 && (a75 == 32 && (a173 == 35 && (a256 == 32 && a240 != 1)))) && (((-65 < a382) && (-39 >= a382)) && ((a338 == 4 && (a91 == 8 && (a102 == a127[6] && (input == inputs[9] && cf == 1)))) && a361 == 32)))) {
		a164 += (a164 + 20) > a164 ? 1 : 0;
		cf = 0;
		a239 = a268;
		a225 = a205[(a230 + -5)];
		a395 = 0;
		a201 = (((21 + -75) + -6223) + 6255);
		a339 = 0;
		a218 = 34;
		a269 = 34;
		a256 = 33;
		a338 = (a270 + -6);
		a302 = a346[((a237 + a338) - 7)];
		a228 = a292;
		a249 = (((((((a249 * a357) % 14999) % 71) + 428) * 5) % 71) + 359);
		a260 = 0;
		a373 = 1;
		a358 = a335;
		a361 = 34;
		a313 = 34;
		a57 = (a91 - -4);
		a336 = 1;
		a207 = 32;
		a296 = a362;
		a329 = 34;
		a310 = ((((((((a357 * a277) % 14999) % 20) + 337) - 14732) * 2) % 20) - -351);
		a368 = 1;
		a320 = ((a206 * a206) + -28);
		a270 = (a237 - -7);
		a398 = (a230 - -6);
		a392 = a304;
		a158 = (a237 - -1);
		a382 = ((((((a382 * a277) % 107) - -121) - -3535) - 3420) - 79);
		a81 = a167[(a57 - 10)];
		a211 = (a320 - 5);
		a75 = 34;
		a240 = 1;
		a265 = a303;
		a357 = (((((((a357 * a310) % 14999) / 5) - -18427) - -8483) % 38) - 37);
		a234 = a372[(a237 + -4)];
		a333 = ((((((a243 * a249) % 14999) + -11579) - -13618) % 14) + 161);
		a312 = 34;
		a276 = a250;
		a386 = ((((((((a249 * a310) % 14999) + 9424) % 61) + 241) / 5) * 45) / 10);
		a237 = ((a359 - a359) + 3);
	}
}
void calculate_outputm86(int input) {
	if ((((input == inputs[7] && (a395 != 1 && ((a91 == 11 && cf == 1) && a75 == 32))) && (50 == a228[0])) && ((50 == a228[0]) && ((53 == a265[5]) && (a173 == 35 && (a1 == a87[6] && (a307 == a227[1] && ((152 < a249) && (355 >= a249))))))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a173 = 33;
		a338 = 7;
		a225 = a205[6];
		a249 = (((a249 - -6822) + 18468) - 32006);
		a201 = (((a201 / 5) + 5659) / 5);
		a130 = (((25 / 5) - 1541) - -127);
		a333 = (((a333 + -26089) / 5) - -30298);
		a276 = a250;
		a336 = 0;
		a361 = 36;
		a398 = 14;
		a373 = 0;
		a207 = 34;
		a256 = 36;
		a300 = 1;
		a329 = 34;
		a202 = a217[2];
		a353 = a241;
		a296 = a362;
		a265 = a376;
		a191 = a37[(a211 - -4)];
	}
	if (((((((160 < a310) && (316 >= a310)) && a300 != 1) && a230 == 4) && a1 == a87[6]) && (((a336 != 1 && (a75 == 32 && ((a91 == 11 && (cf == 1 && a173 == 35)) && a234 == a372[1]))) && input == inputs[6]) && a383 == a226[1]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a5 -= (a5 - 20) < a5 ? 3 : 0;
		cf = 0;
		if (((!(a75 == 35) || (76 == a358[5])) || a240 != 1)) {
			a269 = 32;
			a329 = 36;
			a228 = a264;
			a312 = 33;
			a239 = a299;
			a373 = 1;
			a333 = (((a333 + 13224) * 2) - -2005);
			a336 = 1;
			a286 = a294[3];
			a225 = a205[3];
			a243 = (((76 / 5) + 7002) + 9365);
			a296 = a212;
			a210 = 0;
			a211 = 1;
			a358 = a351;
			a338 = 7;
			a207 = 36;
			a256 = 32;
			a307 = a227[4];
			a173 = 32;
			a237 = 4;
			a235 = a216[5];
			a249 = ((((((a249 + 9780) % 71) + 395) * 5) % 71) - -393);
			a339 = 1;
			a302 = a346[0];
			a260 = 0;
			a277 = ((((a277 + 16042) * 1) * 10) / 9);
			a353 = a399;
			a125 = a30[((a398 - a91) - -4)];
		} else {
			a57 = (a91 + 5);
			a134 = 1;
			a75 = 34;
			a278 = a326[((a270 / a57) - -6)];
		}
	}
	if ((((43 == a392[3]) && ((103 == a276[1]) && a336 != 1)) && ((11 == a353[4]) && ((a75 == 32 && (a378 != 1 && (a1 == a87[6] && ((input == inputs[2] && (cf == 1 && a91 == 11)) && a173 == 35)))) && a218 == 32)))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		if (a129 == a92[0]) {
			a75 = 34;
			a57 = (a91 + 3);
			a134 = 0;
			a71 = a175[((a206 * a320) - 31)];
		} else {
			a1 = a87[((a206 + a91) - 12)];
		}
	}
	if (((a302 == a346[1] && (a395 != 1 && input == inputs[4])) && ((((a398 == 11 && (a173 == 35 && (a75 == 32 && ((cf == 1 && a1 == a87[6]) && a91 == 11)))) && a359 == 4) && ((-199 < a201) && (-12 >= a201))) && a368 != 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a35 -= (a35 - 20) < a35 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a312 = 35;
		a107 = 33;
		a256 = 35;
		a378 = 0;
		a225 = a205[5];
		a173 = 32;
		a336 = 0;
		a207 = 35;
		a338 = 5;
		a125 = a30[(a230 - -2)];
	}
	if (((a75 == 32 && ((77 < a386) && (201 >= a386))) && ((76 == a358[5]) && ((((((((a173 == 35 && cf == 1) && a91 == 11) && a1 == a87[6]) && input == inputs[8]) && a302 == a346[1]) && (50 == a228[0])) && (11 == a353[4])) && ((77 < a386) && (201 >= a386)))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a98 += (a98 + 20) > a98 ? 3 : 0;
		a162 -= (a162 - 20) < a162 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		a91 = (a359 - -9);
		a195 = a58;
	}
	if (((a339 != 1 && ((a1 == a87[6] && (((cf == 1 && a173 == 35) && input == inputs[1]) && a91 == 11)) && a234 == a372[1])) && (((-65 < a382) && (-39 >= a382)) && (((a206 == 5 && a378 != 1) && a75 == 32) && ((160 < a310) && (316 >= a310)))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 4 : 0;
		cf = 0;
		a211 = 6;
		a235 = a216[3];
		a276 = a250;
		a395 = 0;
		a386 = (((((a386 * 5) + 19875) + -47572) % 61) + 314);
		a383 = a226[1];
		a158 = (a91 - 5);
		a333 = (((((a333 - 13011) * 2) - 1241) % 14) + 172);
		a368 = 0;
		a324 = a232[4];
		a382 = ((((a382 * 10) / 6) * 5) - 6303);
		a243 = (((19 - 178) + 23459) + -23465);
		a277 = ((((a277 % 78) - -68) - -2) - 1);
		a353 = a241;
		a339 = 1;
		a228 = a264;
		a75 = 34;
		a237 = 9;
		a218 = 33;
		a358 = a351;
		a57 = (a359 - -6);
		a240 = 0;
		a392 = a304;
		a398 = 13;
		a270 = 16;
		a373 = 0;
		a260 = 0;
		a206 = 5;
		a202 = a217[1];
		a307 = a227[3];
		a357 = (((a357 - -22398) + 7170) - 39258);
		a378 = 0;
		a312 = 35;
		a230 = 5;
		a336 = 0;
		a269 = 35;
		a302 = a346[5];
		a320 = 6;
		a201 = (((a201 + 6798) - -13238) * 1);
		a361 = 35;
		a105 = 34;
		a370 = a311;
		a310 = (((a310 + -5355) + -3540) - 11662);
		a239 = a268;
		a313 = 35;
		a359 = 4;
	}
	if (((((160 < a310) && (316 >= a310)) && (a395 != 1 && (a1 == a87[6] && ((a75 == 32 && cf == 1) && input == inputs[5])))) && (a202 == a217[1] && ((a313 == 32 && ((11 == a353[4]) && (((160 < a310) && (316 >= a310)) && a91 == 11))) && a173 == 35)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a67 -= (a67 - 20) < a67 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if ((!(a141 == a47[6]) || (a134 != 1 && a206 == 10))) {
			a173 = 34;
			a234 = a372[3];
			a172 = (a320 - 6);
			a243 = (((91 + 18269) + 4975) + 4723);
			a296 = a362;
			a353 = a263;
			a329 = 35;
			a339 = 0;
			a207 = 34;
			a338 = 6;
			a211 = 6;
			a225 = a205[6];
			a256 = 36;
			a269 = 34;
			a129 = a92[((a206 - a91) + 13)];
		} else {
			a265 = a303;
			a239 = a242;
			a57 = ((a91 + a91) + -9);
			a313 = 35;
			a230 = 9;
			a269 = 32;
			a386 = (((((a386 * -5) * 10) / 9) - -7777) * -4);
			a277 = (((a277 + 6416) / 5) + 3146);
			a234 = a372[5];
			a323 = (a211 - -5);
			a312 = 32;
			a373 = 1;
			a228 = a229;
			a358 = a348;
			a218 = 32;
			a249 = (((((((a249 * 33) / 10) * 10) / 9) - 9592) * -1) / 10);
			a383 = a226[6];
			a276 = a289;
			a224 = 35;
			a137 = a117;
			a307 = a227[0];
			a243 = ((((18 - 13823) + 16388) * 10) / 9);
			a336 = 0;
			a339 = 1;
			a353 = a263;
			a357 = (((a357 + -6497) - -36442) - 31541);
			a392 = a208;
			a368 = 0;
			a225 = a205[3];
			a300 = 0;
			a398 = 16;
			a260 = 0;
			a359 = 9;
			a270 = 13;
			a378 = 0;
			a237 = 3;
			a75 = 34;
			a201 = ((((a201 % 93) + -88) + 23803) + -23782);
			a206 = 4;
			a296 = a362;
			a320 = 13;
			a310 = (((((a310 - -29477) - 22656) / 5) * 2) / 10);
			a240 = 0;
			a333 = (((a333 + 23570) - -4357) * 1);
			a211 = 2;
		}
	}
	if (((a75 == 32 && ((((43 == a392[3]) && (a339 != 1 && a336 != 1)) && a1 == a87[6]) && a91 == 11)) && ((((a173 == 35 && (input == inputs[3] && cf == 1)) && a218 == 32) && a230 == 4) && a260 != 1))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a178 += (a178 + 20) > a178 ? 3 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if (((a397 == 8 && (!(21 == a46[0]) || (a125 == a30[4] || a307 == 7))) && a240 == 1)) {
			a99 = a26[(a91 + -10)];
			a75 = 34;
			a57 = (a270 + 1);
			a81 = a167[(a91 + -11)];
		} else {
			a224 = 36;
			a373 = 1;
			a353 = a241;
			a383 = a226[3];
			a75 = 34;
			a395 = 0;
			a230 = 4;
			a278 = a326[((a359 - a91) + 9)];
			a240 = 0;
			a277 = (((a277 + 24884) - -4522) + 406);
			a357 = ((((a357 * 10) / -9) - 3277) - -23773);
			a269 = 35;
			a336 = 0;
			a40 = a65;
			a302 = a346[3];
			a218 = 33;
			a320 = 11;
			a307 = a227[1];
			a239 = a242;
			a57 = ((a206 - a398) - -22);
		}
	}
	if ((((a324 == a232[1] && (a218 == 32 && (input == inputs[9] && (a173 == 35 && (cf == 1 && a1 == a87[6]))))) && ((-47 < a333) && (147 >= a333))) && (a224 == 32 && (a224 == 32 && ((a373 != 1 && a91 == 11) && a75 == 32))))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		a161 -= (a161 - 20) < a161 ? 2 : 0;
		cf = 0;
		a295 = a366[(a91 + -6)];
		a75 = 35;
		a134 = 0;
		a53 = (((((29 * 10) / 1) / 5) * 31) / 10);
	}
	if ((((a91 == 11 && (((-10 < a277) && (148 >= a277)) && ((input == inputs[0] && (cf == 1 && a75 == 32)) && (40 == a239[3])))) && (53 == a265[5])) && (((-47 < a333) && (147 >= a333)) && ((((-199 < a201) && (-12 >= a201)) && (((-199 < a201) && (-12 >= a201)) && a173 == 35)) && a1 == a87[6])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a63 -= (a63 - 20) < a63 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		a141 = a47[((a237 * a206) + -19)];
		a57 = (a398 - -4);
		a75 = 34;
		a72 = ((((92 * 10) / -8) + -2697) / 5);
	}
}
void calculate_outputm87(int input) {
	if ((((a320 == 7 && ((a142 != 1 && (a91 == 12 && cf == 1)) && a75 == 32)) && a338 == 4) && ((((160 < a310) && (316 >= a310)) && (a300 != 1 && (a383 == a226[1] && (input == inputs[2] && ((77 < a386) && (201 >= a386)))))) && a173 == 35))) {
		a174 += (a174 + 20) > a174 ? 3 : 0;
		cf = 0;
		a125 = a30[(a237 - 4)];
		a173 = 32;
		a361 = 32;
		a234 = a372[(a237 + -2)];
		a224 = 33;
		a54 = (((((28 + -3250) / 5) / 5) * -32) / 10);
		a225 = a205[(a359 + -4)];
		a383 = a226[((a211 * a91) + -24)];
	}
}
void calculate_outputm89(int input) {
	if (((((152 < a249) && (355 >= a249)) && (input == inputs[5] && (a324 == a232[1] && ((77 < a386) && (201 >= a386))))) && (a234 == a372[1] && ((a173 == 35 && (a336 != 1 && (((a97 == 1 && cf == 1) && a75 == 32) && a329 == 32))) && a91 == 14)))) {
		a120 -= (a120 - 20) < a120 ? 2 : 0;
		cf = 0;
		a201 = ((((((a357 * a333) % 93) + -104) / 5) - -25829) + -25864);
		a392 = a257;
		a286 = a294[(a206 + -2)];
		a240 = 0;
		a256 = 34;
		a329 = 34;
		a277 = ((((((a277 * a333) * 1) % 78) + 69) - -13849) + -13849);
		a324 = a232[((a211 + a359) - 5)];
		a357 = ((((((a249 * a249) % 14999) - 4301) % 65) - 121) + -2);
		a358 = a348;
		a237 = (a270 - 8);
		a235 = a216[(a398 + -10)];
		a171 = 36;
		a338 = a230;
		a211 = ((a398 * a338) + -32);
		a134 = 0;
		a378 = 1;
		a234 = a372[(a206 - 4)];
		a395 = 1;
		a260 = 0;
		a320 = (a237 + 3);
		a224 = 33;
		a368 = 0;
		a270 = ((a91 - a211) - 2);
		a218 = 33;
		a302 = a346[(a206 + -3)];
		a373 = 0;
		a265 = a376;
		a336 = 1;
		a383 = a226[(a206 + -2)];
		a295 = a366[(a91 - 12)];
		a313 = 32;
		a207 = 33;
		a382 = (((((((a310 * a249) % 14999) % 12) + -60) / 5) + -18673) - -18636);
		a269 = 33;
		a307 = a227[(a398 + -10)];
		a312 = 32;
		a296 = a384;
		a300 = 1;
		a353 = a263;
		a370 = a285;
		a225 = a205[((a91 * a91) - 195)];
		a75 = 35;
		a310 = ((((((a310 * a386) % 14999) % 77) + 191) - -27) - 2);
		a361 = 32;
		a333 = (((((((a333 * a243) % 14999) - -5415) % 14976) + -15022) - -20272) - 20274);
		a228 = a229;
		a398 = (a206 - -7);
		a386 = (((((((((a386 * a249) % 14999) % 61) - -111) * 10) / 9) * 5) % 61) - -97);
		a249 = ((((a249 % 101) + 243) - -7549) + -7601);
	}
	if ((((((a302 == a346[1] && a235 == a216[1]) && a173 == 35) && input == inputs[6]) && ((-188 < a357) && (-57 >= a357))) && (a307 == a227[1] && (((11 == a353[4]) && (a75 == 32 && ((cf == 1 && a97 == 1) && a91 == 14))) && a398 == 11)))) {
		cf = 0;
		a286 = a294[(a320 / a320)];
		a339 = 0;
		a239 = a299;
		a142 = 0;
		a333 = (((((a333 * a277) / 5) % 96) - -51) - 1);
		a302 = a346[(a320 - 6)];
		a260 = 0;
		a373 = 0;
		a206 = (a398 - 6);
		a265 = a293;
		a370 = a285;
		a202 = a217[((a270 + a270) + -21)];
		a243 = ((((((a277 * a386) - 670) % 11) - 167) - 27770) + 27770);
		a329 = 32;
		a398 = ((a270 * a270) + -110);
		a201 = ((((((a277 * a277) % 93) + -104) / 5) - -19472) - 19507);
		a359 = ((a320 / a320) - -3);
		a353 = a399;
		a91 = (a211 + 10);
		a382 = (((((((a357 * a249) % 14999) % 12) + -50) - 3) - -4934) - 4931);
		a276 = a289;
		a324 = a232[(a211 + -1)];
		a336 = 0;
		a358 = a351;
		a307 = a227[(a320 - 6)];
		a228 = a229;
		a230 = a338;
		a207 = 32;
		a235 = a216[(a237 - 3)];
		a312 = 32;
		a277 = (((((((a277 * a249) % 14999) % 95) - -243) * 5) % 95) - -234);
	}
}
void calculate_outputm6(int input) {
	if (((((a329 == 32 && ((-199 < a201) && (-12 >= a201))) && a230 == 4) && a235 == a216[1]) && (a338 == 4 && (a302 == a346[1] && (cf == 1 && a91 == 7))))) {
		if (((((((cf == 1 && a59 == 33) && a361 == 32) && a383 == a226[1]) && a260 != 1) && a324 == a232[1]) && (a339 != 1 && ((160 < a310) && (316 >= a310))))) {
			calculate_outputm81(input);
		}
	}
	if ((((a320 == 7 && ((cf == 1 && a91 == 8) && (76 == a358[5]))) && a336 != 1) && (a338 == 4 && (((152 < a249) && (355 >= a249)) && a302 == a346[1])))) {
		if ((((a102 == a127[5] && cf == 1) && a359 == 4) && ((((a206 == 5 && a378 != 1) && ((-65 < a382) && (-39 >= a382))) && a235 == a216[1]) && ((-179 < a243) && (-156 >= a243))))) {
			calculate_outputm82(input);
		}
		if ((((103 == a276[1]) && ((a218 == 32 && (a102 == a127[6] && cf == 1)) && a302 == a346[1])) && (a234 == a372[1] && (a211 == 2 && a240 != 1)))) {
			calculate_outputm83(input);
		}
	}
	if ((((((28 == a370[0]) && a307 == a227[1]) && (40 == a239[3])) && a313 == 32) && ((a361 == 32 && (cf == 1 && a91 == 11)) && (11 == a353[4])))) {
		if ((((40 == a239[3]) && (a324 == a232[1] && (cf == 1 && a1 == a87[6]))) && (a378 != 1 && (a398 == 11 && (a206 == 5 && ((-65 < a382) && (-39 >= a382))))))) {
			calculate_outputm86(input);
		}
	}
	if ((((a91 == 12 && cf == 1) && a395 != 1) && (((a256 == 32 && (a378 != 1 && a368 != 1)) && ((152 < a249) && (355 >= a249))) && a240 != 1))) {
		if (((a225 == a205[1] && a218 == 32) && (a224 == 32 && ((((cf == 1 && a142 != 1) && (89 == a296[5])) && a234 == a372[1]) && a269 == 32)))) {
			calculate_outputm87(input);
		}
	}
	if (((((-47 < a333) && (147 >= a333)) && (((a91 == 14 && cf == 1) && ((-10 < a277) && (148 >= a277))) && a383 == a226[1])) && ((a312 == 32 && a383 == a226[1]) && (50 == a228[0])))) {
		if ((((((((-10 < a277) && (148 >= a277)) && (a97 == 1 && cf == 1)) && a395 != 1) && ((-188 < a357) && (-57 >= a357))) && a207 == 32) && (a270 == 11 && (76 == a358[5])))) {
			calculate_outputm89(input);
		}
	}
}
void calculate_outputm90(int input) {
	if (((a123 != 1 && ((a207 == 32 && a329 == 32) && a141 == a47[0])) && (((((((cf == 1 && input == inputs[9]) && a173 == 36) && a373 != 1) && a368 != 1) && a234 == a372[1]) && a320 == 7) && a75 == 32))) {
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		cf = 0;
		a353 = a399;
		a173 = 32;
		a269 = 34;
		a129 = a92[(a270 - 4)];
		a218 = 34;
		a358 = a335;
		a383 = a226[a211];
		a125 = a30[((a206 - a206) + 7)];
		a302 = a346[(a320 - 5)];
		a249 = (((((a249 * a333) % 14999) + -14913) - 15) + -65);
		a256 = 34;
		a368 = 1;
		a307 = a227[(a237 - 2)];
		a333 = (((((a333 * a277) % 14) + 162) / 5) + 141);
	}
	if ((((76 == a358[5]) && ((a75 == 32 && ((cf == 1 && input == inputs[1]) && a141 == a47[0])) && a173 == 36)) && (((a373 != 1 && ((a123 != 1 && a307 == a227[1]) && (43 == a392[3]))) && ((152 < a249) && (355 >= a249))) && a270 == 11))) {
		a94 += (a94 + 20) > a94 ? 4 : 0;
		cf = 0;
		a172 = a230;
		a173 = 34;
		a274 = a290;
	}
}
void calculate_outputm93(int input) {
	if ((((((((a378 != 1 && a75 == 32) && ((-188 < a357) && (-57 >= a357))) && input == inputs[6]) && ((-10 < a277) && (148 >= a277))) && a42 == 8) && (103 == a276[1])) && (a256 == 32 && (a324 == a232[1] && ((cf == 1 && a141 == a47[1]) && a173 == 36))))) {
		cf = 0;
		a310 = ((((((a310 * a386) % 14999) + -7762) / 5) / 5) - 23752);
		a324 = a232[(a270 - 11)];
		a307 = a227[(a211 - 1)];
		a151 = 1;
		a395 = 1;
		a75 = 36;
		a277 = ((((((a277 * a310) % 14999) / 5) + -16410) * 10) / 9);
		a146 = 1;
		a313 = 33;
		a270 = (a338 - -7);
		a260 = 1;
		a46 = a119;
	}
}
void calculate_outputm96(int input) {
	if (((a234 == a372[1] && (a218 == 32 && (((a184 == a157[6] && (a75 == 32 && (input == inputs[8] && cf == 1))) && a324 == a232[1]) && a141 == a47[3]))) && ((a302 == a346[1] && (a373 != 1 && a173 == 36)) && (53 == a265[5])))) {
		a161 -= (a161 - 20) < a161 ? 2 : 0;
		cf = 0;
		a234 = a372[(a320 - 6)];
		a270 = (a206 + 6);
		a57 = 15;
		a307 = a227[(a206 + -4)];
		a265 = a376;
		a75 = 34;
		a224 = 33;
		a218 = 34;
		a237 = (a320 + -3);
		a240 = 1;
		a373 = 0;
		a392 = a304;
		a313 = 34;
		a329 = 33;
		a336 = 1;
		a201 = ((((((a201 * a249) % 14999) + 23721) + 4035) % 94) + -10);
		a368 = 1;
		a302 = a346[((a320 + a320) - 14)];
		a324 = a232[(a398 - 9)];
		a72 = (((8 + -21335) + -7672) - 67);
		a398 = (a230 - -5);
		a357 = (((((((a357 * a243) % 38) + -27) * 5) * 5) % 38) - 17);
	}
}
void calculate_outputm97(int input) {
	if ((((((((a75 == 32 && cf == 1) && a184 == a157[7]) && a260 != 1) && a286 == a294[1]) && a141 == a47[3]) && ((((77 < a386) && (201 >= a386)) && (((160 < a310) && (316 >= a310)) && (a286 == a294[1] && (input == inputs[4] && ((-188 < a357) && (-57 >= a357)))))) && a173 == 36)) && a89 == 9776)) {
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		cf = 0;
		a172 = ((a359 + a320) + -9);
		a173 = 34;
		a8 = (a172 + 4);
	}
	if ((((a184 == a157[7] && (input == inputs[6] && a373 != 1)) && a224 == 32) && ((((a173 == 36 && (a395 != 1 && (a141 == a47[3] && (a75 == 32 && cf == 1)))) && ((152 < a249) && (355 >= a249))) && a395 != 1) && a237 == 4))) {
		a51 += (a51 + 20) > a51 ? 3 : 0;
		cf = 0;
		a296 = a212;
		a218 = 33;
		a373 = 1;
		a312 = 33;
		a358 = a348;
		a310 = ((((((a310 * a386) % 14999) + -16100) + 19318) + 5205) * -1);
		a276 = a253;
		a336 = 1;
		a307 = a227[(a320 - 7)];
		a320 = (a211 + 4);
		a295 = a366[(a398 + -7)];
		a134 = 0;
		a224 = 33;
		a75 = 35;
		a201 = (((((a201 * a333) % 14999) + -19452) / 5) - 12276);
		a202 = a217[(a206 - 5)];
		a359 = ((a230 * a270) - 41);
		a184 = a157[3];
	}
	if (((a75 == 32 && (((((input == inputs[5] && (a184 == a157[7] && cf == 1)) && a141 == a47[3]) && a234 == a372[1]) && a173 == 36) && (89 == a296[5]))) && (((((77 < a386) && (201 >= a386)) && ((77 < a386) && (201 >= a386))) && a329 == 32) && a225 == a205[1]))) {
		a131 += (a131 + 20) > a131 ? 2 : 0;
		a169 += (a169 + 20) > a169 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 2 : 0;
		a90 += (a90 + 20) > a90 ? 6 : 0;
		a110 += (a110 + 20) > a110 ? 2 : 0;
		a31 -= (a31 - 20) < a31 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 2 : 0;
		a174 += (a174 + 20) > a174 ? 3 : 0;
		cf = 0;
		a256 = 32;
		a373 = 0;
		a269 = 32;
		a57 = (a230 - -9);
		a307 = a227[((a57 / a338) + -1)];
		a260 = 1;
		a277 = ((((((((a386 * a386) % 14999) + -5853) % 95) - -243) * 5) % 95) - -236);
		a234 = a372[(a230 + -2)];
		a218 = 34;
		a276 = a250;
		a302 = a346[(a57 - 11)];
		a382 = (((((a382 * a310) / 5) % 107) + 102) + 15);
		a202 = a217[((a206 + a338) - 7)];
		a395 = 1;
		a137 = a189;
		a358 = a335;
		a249 = ((((((a386 * a201) % 14999) % 71) - -428) / 5) + 344);
		a211 = ((a57 - a359) - 6);
		a243 = ((((((a249 * a382) % 14999) / 5) % 11) - 167) + 1);
		a339 = 0;
		a239 = a268;
		a333 = ((((((((a201 * a201) % 14999) + -5530) % 14) + 161) * 5) % 14) + 161);
		a398 = (a320 - -5);
		a357 = (((((((a357 * a249) % 14999) - -15800) / 5) - -17520) % 38) + -21);
		a207 = 34;
		a392 = a304;
		a228 = a292;
		a240 = 1;
		a383 = a226[(a57 - 11)];
		a265 = a376;
		a324 = a232[(a206 + -3)];
		a224 = 34;
		a353 = a399;
		a237 = (a270 - 6);
		a312 = 34;
		a361 = 34;
		a270 = ((a338 / a206) + 12);
		a329 = 34;
		a320 = (a57 - 5);
		a359 = ((a57 - a57) + 5);
		a336 = 1;
		a225 = a205[(a57 - 11)];
		a338 = (a57 + -8);
		a230 = (a57 + -8);
		a313 = 34;
		a370 = a311;
		a75 = 34;
		a378 = 0;
		a235 = a216[(a237 + -4)];
		a286 = a294[(a398 - 10)];
		a296 = a362;
		a206 = ((a57 + a57) + -20);
		a386 = ((((((((a386 * a333) % 14999) % 61) - -262) / 5) / 5) * 229) / 10);
		a300 = 0;
		a154 = (a57 + 3);
	}
	if ((((((152 < a249) && (355 >= a249)) && (a230 == 4 && (a202 == a217[1] && (a141 == a47[3] && ((77 < a386) && (201 >= a386)))))) && ((76 == a358[5]) && ((a184 == a157[7] && (a320 == 7 && (a173 == 36 && (a75 == 32 && cf == 1)))) && input == inputs[0]))) && a63 >= 3)) {
		a178 += (a178 + 20) > a178 ? 2 : 0;
		cf = 0;
		a224 = 34;
		a206 = (a211 - -4);
		a357 = ((((((a386 * a249) % 14999) % 38) - 20) - 10015) - -10000);
		a57 = (a270 + 5);
		a75 = 34;
		a183 = 35;
		a329 = 34;
		a395 = 1;
		a398 = (a230 - -8);
		a239 = a268;
		a307 = a227[(a206 - a338)];
		a353 = a399;
		a336 = 1;
		a218 = 34;
		a310 = (((((a310 * a357) % 20) + 337) + 1) * 1);
		a240 = 1;
		a228 = a292;
		a312 = 34;
		a278 = a326[(a57 - 11)];
		a392 = a304;
		a370 = a311;
		a333 = ((((((a249 * a249) % 14999) - -8901) % 14) - -151) + -1);
	}
	if ((((((28 == a370[0]) && (a312 == 32 && (a184 == a157[7] && a395 != 1))) && ((-188 < a357) && (-57 >= a357))) && (a338 == 4 && (a206 == 5 && (a141 == a47[3] && (((cf == 1 && a75 == 32) && input == inputs[8]) && a173 == 36))))) && a174 <= 3)) {
		a5 -= (a5 - 20) < a5 ? 2 : 0;
		cf = 0;
		a173 = 32;
		a129 = a92[(a270 - 10)];
		a125 = a30[(a211 - -5)];
	}
	if ((((a324 == a232[1] && (a224 == 32 && a202 == a217[1])) && (89 == a296[5])) && (((a237 == 4 && (a173 == 36 && (((cf == 1 && a141 == a47[3]) && a184 == a157[7]) && input == inputs[9]))) && a75 == 32) && ((-65 < a382) && (-39 >= a382))))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 2 : 0;
		a5 += (a5 + 20) > a5 ? 2 : 0;
		a93 += (a93 + 20) > a93 ? 2 : 0;
		a94 -= (a94 - 20) < a94 ? 4 : 0;
		cf = 0;
		a373 = 1;
		a312 = 33;
		a265 = a376;
		a302 = a346[(a338 - 2)];
		a277 = (((((a333 * a333) % 14999) - 29001) + -946) * 1);
		a270 = (a211 + 8);
		a243 = ((((((a277 * a249) % 14999) + -1464) * 10) / 9) - 5172);
		a237 = ((a211 / a270) - -3);
		a276 = a250;
		a398 = (a206 - -5);
		a353 = a263;
		a368 = 1;
		a202 = a217[(a320 - 6)];
		a260 = 1;
		a218 = 33;
		a230 = ((a206 * a206) - 22);
		a357 = (((((a357 * a243) % 14999) - 25959) + -3872) - 79);
		a16 = 1;
		a256 = 34;
		a383 = a226[(a270 - 10)];
		a249 = (((((a201 * a382) + -16647) % 71) - -475) + -11);
		a146 = 0;
		a235 = a216[(a211 - 2)];
		a386 = (((((a386 * a310) % 14999) + -24117) * 1) - 1455);
		a329 = 33;
		a269 = 32;
		a224 = 34;
		a75 = 36;
		a239 = a242;
		a358 = a348;
		a225 = a205[(a206 - 5)];
		a296 = a212;
		a300 = 1;
		a240 = 1;
		a336 = 1;
		a324 = a232[(a398 + -10)];
		a286 = a294[((a359 - a320) - -5)];
		a234 = a372[(a359 - 2)];
		a361 = 33;
		a73 = (((16 - -164) * 1) + 59);
		a206 = ((a270 * a338) - 36);
		a395 = 1;
		a338 = ((a359 - a320) + 6);
		a359 = ((a320 * a320) + -44);
	}
	if (((((((89 == a296[5]) && ((a173 == 36 && (cf == 1 && input == inputs[2])) && a398 == 11)) && a184 == a157[7]) && (11 == a353[4])) && a75 == 32) && (a211 == 2 && ((a141 == a47[3] && a235 == a216[1]) && ((-188 < a357) && (-57 >= a357)))))) {
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		cf = 0;
		a234 = a372[((a270 + a270) + -20)];
		a249 = ((((68 / 5) * 5) + -1842) - -2217);
		a310 = ((((((a310 * a249) % 14999) - -14369) % 20) + 322) * 1);
		a361 = 34;
		a230 = (a270 - 6);
		a265 = a376;
		a211 = ((a270 / a270) + 2);
		a260 = 1;
		a359 = (a270 - 6);
		a353 = a399;
		a373 = 0;
		a329 = 34;
		a302 = a346[(a230 - 3)];
		a307 = a227[(a359 + -3)];
		a202 = a217[(a270 + -9)];
		a378 = 1;
		a382 = (((((a382 * a201) % 107) - 9) - 14) + -3);
		a240 = 1;
		a357 = (((((((a357 * a277) % 14999) - 1687) % 38) + -1) + 19732) + -19720);
		a269 = 34;
		a158 = (a270 - 6);
		a239 = a268;
		a358 = a335;
		a370 = a318;
		a207 = 34;
		a75 = 34;
		a338 = (a270 + -6);
		a225 = a205[(a237 + -2)];
		a235 = a216[((a359 * a206) - 23)];
		a224 = 34;
		a324 = a232[(a320 - 5)];
		a320 = (a270 + -3);
		a395 = 1;
		a57 = (a237 + 6);
		a312 = 34;
		a237 = a359;
		a392 = a304;
		a218 = 34;
		a336 = 1;
		a339 = 0;
		a276 = a253;
		a200 = a115[(a57 + -5)];
		a333 = ((((79 + -14388) - -14467) - 7035) - -7029);
		a296 = a362;
		a398 = (a211 - -9);
		a201 = (((((a243 * a333) % 94) + 84) * 5) / 5);
		a386 = ((((((((a386 * a249) % 14999) + -16743) % 61) + 314) * 5) % 61) - -239);
		a313 = 34;
		a286 = a294[((a338 + a398) + -15)];
		a206 = ((a270 + a270) + -16);
		a270 = (a359 + 7);
	}
	if ((((((((77 < a386) && (201 >= a386)) && (a206 == 5 && a324 == a232[1])) && a75 == 32) && a313 == 32) && (((input == inputs[1] && (a141 == a47[3] && (a173 == 36 && (cf == 1 && a184 == a157[7])))) && a237 == 4) && (40 == a239[3]))) && a165 == 4790)) {
		a67 -= (a67 - 20) < a67 ? 3 : 0;
		cf = 0;
		a57 = (a206 + 10);
		a72 = (((42 - 7943) * 3) * 1);
		a75 = 34;
		a141 = a47[(a57 - 13)];
	}
}
void calculate_outputm98(int input) {
	if (((((cf == 1 && a141 == a47[4]) && a173 == 36) && a75 == 32) && ((a373 != 1 && (a398 == 11 && (((a221 == 1 && (a307 == a227[1] && input == inputs[8])) && (50 == a228[0])) && (43 == a392[3])))) && a320 == 7))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a173 = 32;
		a81 = a167[(a270 - 11)];
		a125 = a30[((a230 + a230) + -3)];
	}
	if ((((a75 == 32 && (a221 == 1 && ((89 == a296[5]) && ((cf == 1 && a173 == 36) && a141 == a47[4])))) && a286 == a294[1]) && (a361 == 32 && ((input == inputs[0] && ((43 == a392[3]) && a302 == a346[1])) && a373 != 1)))) {
		a120 -= (a120 - 20) < a120 ? 2 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if (((a151 == 1 && ((a302 == 10 && a295 == 9) || a368 == 1)) && a64 != 1)) {
			a134 = 0;
			a224 = 32;
			a234 = a372[1];
			a228 = a292;
			a75 = 35;
			a392 = a257;
			a373 = 0;
			a398 = 17;
			a202 = a217[4];
			a295 = a366[((a230 * a359) + -11)];
			a296 = a362;
			a320 = 9;
			a339 = 0;
			a276 = a289;
			a239 = a268;
			a269 = 34;
			a53 = (((55 * 5) + -232) - 14);
			a358 = a351;
			a218 = 35;
			a361 = 32;
			a359 = 5;
		} else {
			a173 = 33;
			a139 = 33;
			a130 = ((((((63 * 44) / 10) * 10) / 9) * 5) - 1200);
		}
	}
	if (((43 == a392[3]) && (a221 == 1 && (a378 != 1 && (a173 == 36 && (a75 == 32 && (((a286 == a294[1] && ((a141 == a47[4] && (cf == 1 && input == inputs[7])) && ((-179 < a243) && (-156 >= a243)))) && a359 == 4) && a286 == a294[1]))))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		a75 = 34;
		a57 = (a398 + -1);
		a158 = ((a57 + a57) - 16);
		a81 = a167[((a57 / a57) - -4)];
	}
	if (((((a221 == 1 && (a141 == a47[4] && (((103 == a276[1]) && ((input == inputs[2] && cf == 1) && a75 == 32)) && a234 == a372[1]))) && a313 == 32) && a383 == a226[1]) && (((103 == a276[1]) && a286 == a294[1]) && a173 == 36))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a173 = 32;
		a129 = a92[(a206 - 4)];
		a125 = a30[(a338 + 3)];
	}
	if (((a206 == 5 && ((a141 == a47[4] && ((a368 != 1 && a338 == 4) && input == inputs[9])) && a221 == 1)) && (((152 < a249) && (355 >= a249)) && (((89 == a296[5]) && (a173 == 36 && (a75 == 32 && cf == 1))) && a286 == a294[1])))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		a237 = 5;
		a313 = 32;
		a57 = (a270 - -1);
		a296 = a384;
		a300 = 0;
		a249 = ((((a249 * 5) * 5) / 5) + -5170);
		a211 = 5;
		a202 = a217[1];
		a239 = a299;
		a378 = 0;
		a81 = a167[((a57 + a270) + -16)];
		a218 = 36;
		a357 = ((((a357 / 5) - 59) / 5) + -139);
		a329 = 33;
		a361 = 33;
		a336 = 0;
		a307 = a227[0];
		a320 = 9;
		a312 = 32;
		a234 = a372[3];
		a373 = 0;
		a235 = a216[7];
		a323 = ((a230 / a359) + 8);
		a228 = a264;
		a265 = a376;
		a382 = (((((29 * -23) / 10) / 5) * 51) / 10);
		a269 = 35;
		a256 = 34;
		a276 = a253;
		a240 = 0;
		a225 = a205[7];
		a338 = 9;
		a302 = a346[7];
		a224 = 33;
		a243 = ((((a243 * 10) / 8) - 19417) / 5);
		a310 = ((((((a310 * 23) / 10) * 10) / 9) / 5) - -20470);
		a230 = 4;
		a277 = (((a277 - 23598) + -2334) - 2035);
		a333 = (((68 + -12098) - 16413) + -1373);
		a339 = 1;
		a358 = a351;
		a370 = a285;
		a368 = 0;
		a324 = a232[6];
		a75 = 34;
		a206 = 11;
		a359 = 4;
	}
	if (((((((((cf == 1 && input == inputs[5]) && a141 == a47[4]) && a173 == 36) && a398 == 11) && a373 != 1) && a221 == 1) && (28 == a370[0])) && ((a260 != 1 && (a75 == 32 && a313 == 32)) && a235 == a216[1]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;

	}
	if (((a260 != 1 && (((cf == 1 && input == inputs[3]) && a173 == 36) && a240 != 1)) && ((a75 == 32 && (a141 == a47[4] && ((a221 == 1 && (a329 == 32 && a359 == 4)) && a234 == a372[1]))) && a300 != 1))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a67 -= (a67 - 20) < a67 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a302 = a346[6];
		a57 = 10;
		a286 = a294[7];
		a382 = ((((58 - 181) / 5) / 5) - 44);
		a329 = 35;
		a265 = a293;
		a224 = 35;
		a300 = 0;
		a336 = 0;
		a158 = (a320 - 2);
		a339 = 1;
		a234 = a372[7];
		a270 = 14;
		a202 = a217[6];
		a358 = a351;
		a260 = 0;
		a383 = a226[6];
		a243 = (((a243 - 5457) * 5) / -5);
		a200 = a115[((a158 - a57) - -10)];
		a75 = 34;
		a313 = 32;
		a201 = (((a201 + 272) - -1369) / 5);
		a310 = ((((a310 % 77) + 175) / 5) + 163);
		a239 = a299;
		a395 = 0;
		a235 = a216[4];
		a361 = 32;
		a225 = a205[0];
		a398 = 16;
		a333 = ((((29 - -6288) - 6242) + 28732) - 28785);
		a206 = 4;
		a373 = 1;
		a269 = 33;
		a368 = 0;
		a211 = 6;
		a249 = (((((a249 / 5) * 167) / 10) * 10) / 9);
		a228 = a264;
		a378 = 0;
		a370 = a311;
		a312 = 32;
		a324 = a232[3];
		a338 = 4;
		a357 = (((((a357 * 5) + -19107) - 3884) * -1) / 10);
		a276 = a250;
		a307 = a227[5];
		a296 = a384;
		a240 = 0;
		a359 = 7;
		a230 = 3;
		a392 = a257;
		a277 = ((((a277 - 4395) * 10) / 9) / 5);
		a218 = 35;
		a320 = 12;
	}
	if ((((a221 == 1 && ((((input == inputs[1] && cf == 1) && a141 == a47[4]) && a173 == 36) && ((-188 < a357) && (-57 >= a357)))) && a324 == a232[1]) && ((((a373 != 1 && a75 == 32) && ((152 < a249) && (355 >= a249))) && (43 == a392[3])) && a260 != 1))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a98 += (a98 + 20) > a98 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a81 = a167[(a398 + -11)];
		a173 = 32;
		a125 = a30[(a270 + -6)];
	}
	if ((((a173 == 36 && a373 != 1) && (40 == a239[3])) && (((a320 == 7 && (((a75 == 32 && ((a221 == 1 && cf == 1) && a141 == a47[4])) && (28 == a370[0])) && a206 == 5)) && input == inputs[6]) && (53 == a265[5])))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a174 += (a174 + 20) > a174 ? 2 : 0;
		a35 += (a35 + 20) > a35 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a72 = (((57 - 1622) * 5) / 5);
		a57 = (a230 - -11);
		a75 = 34;
		a141 = a47[((a57 - a338) - 10)];
	}
	if (((a202 == a217[1] && (((-199 < a201) && (-12 >= a201)) && ((a173 == 36 && a339 != 1) && a300 != 1))) && (a221 == 1 && ((40 == a239[3]) && (((input == inputs[4] && (a75 == 32 && cf == 1)) && a218 == 32) && a141 == a47[4]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a172 = ((a230 - a206) - -5);
		a173 = 34;
		a274 = a290;
	}
}
void calculate_outputm100(int input) {
	if (((((a225 == a205[1] && ((a368 != 1 && a128 == 12) && ((152 < a249) && (355 >= a249)))) && a75 == 32) && a173 == 36) && (a395 != 1 && ((((160 < a310) && (316 >= a310)) && (input == inputs[5] && (cf == 1 && a141 == a47[6]))) && a395 != 1)))) {
		a174 += (a174 + 20) > a174 ? 3 : 0;
		cf = 0;
		if (((16 == a274[1]) || ((!(a307 == a227[3]) || ((47 == a239[4]) || ((-104 < a72) && (100 >= a72)))) || !(a102 == a127[7])))) {
			a225 = a205[(a338 - 4)];
			a277 = (((((a277 * a201) * 1) * 1) % 14995) + -15004);
			a207 = 34;
			a230 = ((a206 * a359) - 15);
			a353 = a399;
			a312 = 33;
			a141 = a47[(a270 + -8)];
			a184 = a157[((a128 + a128) + -18)];
			a359 = (a270 - 8);
			a339 = 1;
			a228 = a292;
			a206 = (a398 - 5);
			a338 = (a270 + -6);
			a333 = ((((((a333 * a249) % 14999) * 2) * 1) % 14) + 161);
			a249 = ((((((a249 * a357) % 14999) % 71) - -427) + 2) + -1);
		} else {
			a265 = a303;
			a333 = (((((((a333 * a310) % 14999) % 14976) + -15022) - 2) + 13725) - 13723);
			a224 = 33;
			a277 = (((((a277 * a201) - -26078) * 1) % 14995) - 15004);
			a307 = a227[((a230 - a206) - -3)];
			a196 = (a398 - -5);
			a276 = a253;
			a269 = 33;
			a353 = a263;
			a295 = a366[(a128 - 12)];
			a359 = (a237 + -1);
			a234 = a372[(a237 + -2)];
			a339 = 1;
			a324 = a232[(a206 - 3)];
			a211 = ((a230 * a230) + -15);
			a207 = 34;
			a312 = 33;
			a206 = (a359 + 3);
			a134 = 0;
			a302 = a346[(a270 - 9)];
			a338 = (a237 + -1);
			a237 = (a359 + 2);
			a313 = 34;
			a373 = 0;
			a368 = 1;
			a270 = (a398 - -1);
			a378 = 1;
			a75 = 35;
			a230 = (a398 + -6);
			a240 = 1;
			a357 = ((((((a357 * a249) % 14999) % 38) + -17) / 5) - -12);
			a329 = 33;
			a320 = (a338 - -3);
			a398 = (a359 - -7);
			a218 = 33;
			a249 = ((((((((a333 * a201) % 14999) + 4384) % 71) - -382) * 5) % 71) + 420);
			a336 = 1;
			a228 = a229;
			a225 = a205[(a359 + -3)];
			a392 = a208;
			a201 = (((((a201 * a333) % 14999) / 5) + -16438) + 6427);
		}
	}
	if (((((a173 == 36 && ((a128 == 12 && (((cf == 1 && input == inputs[3]) && a141 == a47[6]) && a75 == 32)) && ((160 < a310) && (316 >= a310)))) && a361 == 32) && (11 == a353[4])) && (a312 == 32 && (a234 == a372[1] && (50 == a228[0]))))) {
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		cf = 0;
		a207 = 34;
		a260 = 1;
		a206 = (a128 + -6);
		a224 = 34;
		a373 = 0;
		a398 = a128;
		a228 = a292;
		a386 = (((((((a310 * a310) % 14999) / 5) % 61) - -206) / 5) - -235);
		a218 = 34;
		a237 = (a398 + -7);
		a383 = a226[(a206 + -4)];
		a75 = 34;
		a256 = 34;
		a235 = a216[((a270 / a128) - -1)];
		a265 = a376;
		a338 = ((a237 - a270) + 11);
		a234 = a372[((a398 / a398) - -1)];
		a240 = 1;
		a320 = a206;
		a201 = (((((((a201 * a310) % 14999) + -6289) % 94) - -143) + 23606) + -23571);
		a312 = 33;
		a357 = (((((((a357 * a310) % 14999) + 8412) % 38) - 17) + -22492) - -22491);
		a368 = 1;
		a57 = (a128 - -1);
		a296 = a212;
		a323 = (a128 + -5);
		a358 = a335;
		a339 = 0;
		a202 = a217[((a270 + a128) + -22)];
		a313 = 34;
		a230 = (a270 + -6);
		a239 = a268;
		a307 = a227[(a57 - 11)];
		a382 = ((((((a310 * a249) % 14999) % 12) + -51) + 13434) - 13433);
		a333 = ((((((a333 * a243) + 3711) / 5) / 5) % 14) - -161);
		a329 = 34;
		a392 = a304;
		a353 = a399;
		a336 = 1;
		a277 = (((((a277 * a243) % 95) - -243) - 0) * 1);
		a137 = a117;
		a249 = (((((((a249 * a310) % 14999) % 71) - -366) + 27) / 5) - -288);
		a359 = (a211 - -2);
		a310 = ((((((a310 * a386) % 14999) - 22539) * 1) % 20) - -339);
		a270 = (a323 - -5);
	}
	if (((a234 == a372[1] && ((input == inputs[6] && (a75 == 32 && (a141 == a47[6] && ((a128 == 12 && cf == 1) && a173 == 36)))) && ((-47 < a333) && (147 >= a333)))) && (a339 != 1 && (a256 == 32 && (a207 == 32 && a359 == 4))))) {
		a161 -= (a161 - 20) < a161 ? 4 : 0;
		cf = 0;
		if ((a395 == 1 && (a218 == 35 || a171 == 35))) {
			a57 = (a206 - -6);
			a300 = 0;
			a270 = ((a128 * a338) - 36);
			a333 = (((((((a333 * a310) % 14999) % 14) + 162) / 5) - 21623) + 21749);
			a359 = (a270 - 7);
			a378 = 0;
			a206 = (a57 - 5);
			a211 = (a320 + -6);
			a256 = 34;
			a143 = 32;
			a361 = 34;
			a383 = a226[(a270 - 10)];
			a218 = 34;
			a202 = a217[(a57 + -9)];
			a277 = (((((a277 * a357) / 5) * 5) % 95) + 243);
			a357 = (((((((a382 * a249) % 14999) % 38) + -17) - -8676) + 1180) + -9857);
			a239 = a268;
			a302 = a346[((a359 + a237) - 7)];
			a14 = a79[((a57 * a128) - 130)];
			a353 = a399;
			a358 = a335;
			a75 = 34;
			a230 = (a338 + 1);
			a228 = a292;
			a307 = a227[(a230 - 3)];
			a312 = 34;
			a237 = (a398 + -6);
			a392 = a304;
			a398 = (a320 + 4);
			a338 = (a320 + -3);
			a224 = 34;
			a201 = (((((((a201 * a310) % 14999) / 5) % 94) + 83) - 12411) + 12410);
			a240 = 1;
			a310 = ((((((a310 * a249) % 14999) / 5) % 20) - -332) + 6);
			a249 = (((((a249 * a243) % 14999) - 14613) - 20) / 5);
		} else {
			a276 = a253;
			a383 = a226[(a230 + -4)];
			a382 = ((((29 - -24623) - 24696) - -23517) - 23517);
			a239 = a268;
			a256 = 34;
			a296 = a212;
			a320 = (a398 - 5);
			a228 = a229;
			a184 = a157[((a338 + a237) + -1)];
			a359 = (a128 - 9);
			a357 = ((((((a310 * a310) % 14999) / 5) - 27930) - -41678) + -38437);
			a339 = 1;
			a295 = a366[((a398 * a270) + -117)];
			a370 = a318;
			a249 = ((((a249 / 5) - -12080) / 5) * -5);
			a336 = 1;
			a218 = 33;
			a224 = 33;
			a75 = 35;
			a235 = a216[(a230 + -3)];
			a211 = ((a230 / a230) + 1);
			a373 = 1;
			a240 = 1;
			a237 = ((a206 + a128) - 14);
			a312 = 33;
			a300 = 0;
			a378 = 0;
			a353 = a399;
			a313 = 33;
			a134 = 0;
			a333 = (((((((a333 * a357) % 14999) - -11890) / 5) + 11534) * -1) / 10);
			a307 = a227[(a338 - 2)];
			a338 = ((a206 - a320) - -4);
			a201 = (((((a201 * a310) % 14999) - 1433) - 4126) + -2448);
			a206 = ((a320 / a359) - -2);
			a269 = 33;
			a310 = (((((a310 * a277) % 14999) - 14927) - 27) + -1);
			a260 = 1;
			a398 = (a359 - -7);
		}
	}
}
void calculate_outputm101(int input) {
	if (((((28 == a370[0]) && a338 == 4) && input == inputs[2]) && (((-199 < a201) && (-12 >= a201)) && ((a237 == 4 && (((((cf == 1 && a75 == 32) && a141 == a47[7]) && (11 == a353[4])) && (100 == a275[3])) && a173 == 36)) && a235 == a216[1])))) {
		a67 -= (a67 - 20) < a67 ? 4 : 0;
		cf = 0;
		a383 = a226[(a320 - 7)];
		a225 = a205[(a230 + -4)];
		a173 = 32;
		a353 = a399;
		a234 = a372[(a270 + -9)];
		a125 = a30[(a359 - 4)];
		a361 = 32;
		a224 = 33;
		a54 = ((((77 * 10) / 1) + 22122) * 1);
	}
}
void calculate_outputm7(int input) {
	if (((a312 == 32 && (((-199 < a201) && (-12 >= a201)) && (a141 == a47[0] && cf == 1))) && (a234 == a372[1] && ((a383 == a226[1] && (11 == a353[4])) && a211 == 2)))) {
		if (((a269 == 32 && ((cf == 1 && a123 != 1) && ((-47 < a333) && (147 >= a333)))) && (((a256 == 32 && ((152 < a249) && (355 >= a249))) && ((-10 < a277) && (148 >= a277))) && a235 == a216[1]))) {
			calculate_outputm90(input);
		}
	}
	if (((a269 == 32 && (a141 == a47[1] && cf == 1)) && (((-188 < a357) && (-57 >= a357)) && (((a329 == 32 && a206 == 5) && a207 == 32) && a378 != 1)))) {
		if (((((77 < a386) && (201 >= a386)) && ((a42 == 8 && cf == 1) && a329 == 32)) && (((a286 == a294[1] && a270 == 11) && a307 == a227[1]) && a320 == 7))) {
			calculate_outputm93(input);
		}
	}
	if (((a286 == a294[1] && (a324 == a232[1] && (a307 == a227[1] && (a336 != 1 && (a302 == a346[1] && (a141 == a47[3] && cf == 1)))))) && a237 == 4)) {
		if ((((a398 == 11 && (a373 != 1 && (a184 == a157[6] && cf == 1))) && a302 == a346[1]) && (a286 == a294[1] && (a368 != 1 && ((160 < a310) && (316 >= a310)))))) {
			calculate_outputm96(input);
		}
		if (((a235 == a216[1] && a225 == a205[1]) && ((((53 == a265[5]) && ((cf == 1 && a184 == a157[7]) && a218 == 32)) && ((-65 < a382) && (-39 >= a382))) && a240 != 1))) {
			calculate_outputm97(input);
		}
	}
	if (((a300 != 1 && (a307 == a227[1] && (a300 != 1 && (a141 == a47[4] && cf == 1)))) && (a230 == 4 && ((76 == a358[5]) && a234 == a372[1])))) {
		if (((((((-10 < a277) && (148 >= a277)) && ((-179 < a243) && (-156 >= a243))) && (76 == a358[5])) && a260 != 1) && (((cf == 1 && a221 == 1) && a269 == 32) && (53 == a265[5])))) {
			calculate_outputm98(input);
		}
	}
	if ((((a256 == 32 && a373 != 1) && a270 == 11) && ((((-47 < a333) && (147 >= a333)) && ((a141 == a47[6] && cf == 1) && (28 == a370[0]))) && a230 == 4))) {
		if (((a324 == a232[1] && (a230 == 4 && (a128 == 12 && cf == 1))) && ((50 == a228[0]) && (((-10 < a277) && (148 >= a277)) && (a307 == a227[1] && a230 == 4))))) {
			calculate_outputm100(input);
		}
	}
	if (((a234 == a372[1] && ((-65 < a382) && (-39 >= a382))) && (a225 == a205[1] && ((a286 == a294[1] && (((160 < a310) && (316 >= a310)) && (a141 == a47[7] && cf == 1))) && a260 != 1)))) {
		if (((a202 == a217[1] && (((77 < a386) && (201 >= a386)) && (a230 == 4 && ((100 == a275[3]) && cf == 1)))) && ((103 == a276[1]) && (a395 != 1 && (103 == a276[1]))))) {
			calculate_outputm101(input);
		}
	}
}
void calculate_outputm102(int input) {
	if (((((((cf == 1 && a81 == a167[2]) && a158 == 4) && a338 == 5) && a313 == 34) && a339 != 1) && (a302 == a346[2] && (((a75 == 34 && (a300 == 1 && a57 == 10)) && a234 == a372[2]) && input == inputs[9])))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if ((339 < a277 || a368 == 1)) {
			a75 = 32;
			a173 = 36;
			a184 = a157[((a158 / a237) - -2)];
			a141 = a47[(a57 - 7)];
		} else {
			a132 = 0;
			a155 = 34;
			a75 = 33;
			a77 = ((a206 + a338) - 4);
		}
	}
	if (((a57 == 10 && (((a158 == 4 && (a75 == 34 && cf == 1)) && ((355 < a249) && (499 >= a249))) && a395 == 1)) && (a81 == a167[2] && (((-57 < a357) && (20 >= a357)) && (input == inputs[7] && (((-39 < a382) && (176 >= a382)) && ((59 == a228[3]) && (92 == a296[2])))))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a63 -= (a63 - 20) < a63 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a173 = 35;
		a358 = a335;
		a240 = 1;
		a382 = (((a382 - -24725) + 3547) - -16);
		a91 = (a158 + 4);
		a207 = 33;
		a392 = a304;
		a357 = (((a357 + -14690) * 2) + -282);
		a235 = a216[3];
		a336 = 1;
		a224 = 36;
		a211 = 1;
		a237 = 5;
		a320 = 9;
		a269 = 35;
		a302 = a346[7];
		a361 = 36;
		a338 = 3;
		a234 = a372[4];
		a218 = 35;
		a75 = 32;
		a249 = ((((a249 * 5) + 21089) * 1) * -1);
		a270 = 15;
		a313 = 33;
		a256 = 36;
		a102 = a127[(a91 - 2)];
	}
	if (((a324 == a232[2] && (a383 == a226[2] && (a368 == 1 && (((((-57 < a357) && (20 >= a357)) && a158 == 4) && ((-57 < a357) && (20 >= a357))) && a57 == 10)))) && (a230 == 5 && (a81 == a167[2] && ((cf == 1 && a75 == 34) && input == inputs[6]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a169 -= (a169 - 20) < a169 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		cf = 0;
		a57 = ((a237 / a237) - -14);
		a72 = (((((50 * 9) / 10) * 9) / 10) / 5);
		a36 = ((((((a72 * a72) % 14) - -293) * 5) % 14) - -279);
	}
	if (((((a395 == 1 && ((cf == 1 && a81 == a167[2]) && a75 == 34)) && ((-57 < a357) && (20 >= a357))) && input == inputs[8]) && ((((a312 == 34 && (a158 == 4 && a338 == 5)) && a225 == a205[2]) && a320 == 8) && a57 == 10))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a67 -= (a67 - 20) < a67 ? 4 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a256 = 36;
		a240 = 1;
		a207 = 34;
		a270 = 15;
		a313 = 36;
		a302 = a346[4];
		a386 = ((((a386 - 16272) * 10) / 9) + 15921);
		a97 = 1;
		a357 = (((a357 - 13053) + -4007) * 1);
		a296 = a212;
		a225 = a205[3];
		a307 = a227[4];
		a218 = 35;
		a276 = a289;
		a173 = 35;
		a300 = 1;
		a336 = 1;
		a277 = (((((((a277 * 10) / 4) * 10) / 9) / 5) * 42) / 10);
		a392 = a208;
		a320 = 6;
		a75 = 32;
		a206 = 11;
		a243 = ((((a243 % 11) - 159) + 2) - -1);
		a230 = 9;
		a237 = 5;
		a269 = 34;
		a228 = a229;
		a353 = a399;
		a234 = a372[6];
		a378 = 1;
		a239 = a299;
		a202 = a217[5];
		a249 = (((a249 - -25842) + -41065) * 2);
		a359 = 4;
		a339 = 0;
		a368 = 1;
		a398 = 12;
		a383 = a226[2];
		a312 = 35;
		a211 = 3;
		a358 = a335;
		a333 = ((((a333 + -17815) * 10) / 9) * 1);
		a324 = a232[7];
		a338 = 9;
		a329 = 34;
		a395 = 1;
		a91 = (a57 + 4);
	}
	if (((a225 == a205[2] && (((-156 < a243) && (-68 >= a243)) && ((a307 == a227[2] && input == inputs[3]) && a320 == 8))) && (((a75 == 34 && (a158 == 4 && (a57 == 10 && (cf == 1 && a81 == a167[2])))) && ((201 < a386) && (325 >= a386))) && (38 == a370[4])))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 4 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;

	}
	if ((((a75 == 34 && (a338 == 5 && (a158 == 4 && (input == inputs[0] && (a57 == 10 && cf == 1))))) && a206 == 6) && (((148 < a277) && (339 >= a277)) && (((a81 == a167[2] && ((-39 < a382) && (176 >= a382))) && ((-156 < a243) && (-68 >= a243))) && (15 == a353[2]))))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a35 -= (a35 - 20) < a35 ? 1 : 0;
		a98 -= (a98 - 20) < a98 ? 2 : 0;
		a162 += (a162 + 20) > a162 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		if ((((a151 == 1 && !(76 == a358[5])) || a378 == 1) || !(a183 == 35))) {
			a300 = 1;
			a339 = 1;
			a243 = (((a243 * 5) / -5) / 5);
			a270 = 16;
			a382 = (((a382 / 5) - 8405) - 19449);
			a383 = a226[4];
			a228 = a292;
			a277 = ((((a277 % 95) + 174) + 9976) + -9924);
			a1 = a87[((a57 / a158) - -4)];
			a324 = a232[4];
			a386 = ((((((a386 + 29169) % 61) + 233) * 5) % 61) - -229);
			a286 = a294[6];
			a211 = 1;
			a230 = 9;
			a234 = a372[7];
			a395 = 1;
			a202 = a217[7];
			a392 = a208;
			a249 = (((a249 * -5) - 16509) * 1);
			a235 = a216[5];
			a336 = 1;
			a173 = 35;
			a320 = 11;
			a237 = 10;
			a358 = a348;
			a373 = 1;
			a206 = 10;
			a361 = 33;
			a312 = 36;
			a333 = (((a333 * 5) + -21738) - 5884);
			a239 = a242;
			a75 = 32;
			a218 = 35;
			a307 = a227[3];
			a313 = 35;
			a265 = a303;
			a269 = 35;
			a302 = a346[7];
			a357 = (((((a357 * 5) % 38) - 18) - 7247) - -7247);
			a368 = 1;
			a353 = a399;
			a370 = a318;
			a359 = 5;
			a240 = 1;
			a378 = 1;
			a91 = (a398 + -1);
			a398 = 12;
		} else {
			a173 = 32;
			a81 = a167[(a57 - 7)];
			a75 = 32;
			a125 = a30[(a206 + -1)];
		}
	}
	if (((((((147 < a333) && (177 >= a333)) && input == inputs[4]) && ((147 < a333) && (177 >= a333))) && a57 == 10) && (a368 == 1 && (a81 == a167[2] && (((a313 == 34 && ((a158 == 4 && cf == 1) && a75 == 34)) && a237 == 5) && ((355 < a249) && (499 >= a249))))))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if ((a200 == a115[7] && a99 == 7)) {
			a249 = (((((a249 - 25440) - -21628) - 13821) * -1) / 10);
			a137 = a189;
			a310 = (((79 + 248) * 5) - 1306);
			a286 = a294[0];
			a225 = a205[7];
			a296 = a384;
			a260 = 0;
			a237 = 7;
			a370 = a311;
			a300 = 0;
			a230 = 8;
			a235 = a216[6];
			a320 = 9;
			a224 = 36;
			a265 = a293;
			a361 = 33;
			a373 = 1;
			a154 = a270;
			a206 = 9;
			a201 = (((95 * 5) - -27422) * 1);
			a57 = (a158 + 9);
			a392 = a304;
			a211 = 3;
			a256 = 35;
			a276 = a289;
			a270 = 10;
		} else {
			a353 = a241;
			a225 = a205[2];
			a358 = a335;
			a269 = 35;
			a224 = 36;
			a300 = 0;
			a392 = a304;
			a265 = a293;
			a395 = 0;
			a338 = 5;
			a240 = 0;
			a270 = 16;
			a277 = (((((a277 / 5) - -24107) * 1) * -1) / 10);
			a256 = 34;
			a398 = 12;
			a310 = ((((76 * 5) / 5) - 14021) - -14192);
			a218 = 32;
			a202 = a217[5];
			a207 = 33;
			a239 = a268;
			a378 = 0;
			a228 = a264;
			a368 = 0;
			a249 = (((((a249 % 71) + 418) - 9) + 10826) - 10847);
			a234 = a372[2];
			a312 = 35;
			a230 = 10;
			a75 = 33;
			a286 = a294[4];
			a77 = (a158 + 7);
			a359 = 7;
			a313 = 32;
			a307 = a227[3];
			a320 = 12;
			a361 = 34;
			a132 = 0;
			a276 = a250;
			a206 = 10;
			a373 = 0;
			a370 = a311;
			a243 = ((((((a243 * 5) % 43) + -70) * 5) % 43) + -112);
			a260 = 0;
			a235 = a216[2];
			a211 = 6;
			a237 = 4;
			a99 = a26[(a57 - 3)];
		}
	}
	if ((((a368 == 1 && ((input == inputs[5] && (cf == 1 && a81 == a167[2])) && (56 == a265[2]))) && a368 == 1) && ((a158 == 4 && (((148 < a277) && (339 >= a277)) && (((-57 < a357) && (20 >= a357)) && (a336 == 1 && a75 == 34)))) && a57 == 10))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a162 -= (a162 - 20) < a162 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		a99 = a26[((a57 + a270) + -20)];
		a361 = 34;
		a173 = 34;
		a276 = a289;
		a218 = 35;
		a239 = a268;
		a312 = 33;
		a370 = a318;
		a382 = ((((a382 / 5) - -111) * 9) / 10);
		a373 = 0;
		a320 = 12;
		a225 = a205[4];
		a395 = 1;
		a313 = 35;
		a383 = a226[7];
		a234 = a372[6];
		a338 = 3;
		a230 = 10;
		a300 = 1;
		a368 = 1;
		a240 = 1;
		a256 = 35;
		a296 = a212;
		a357 = (((a357 / 5) + 1584) - -10852);
		a270 = 13;
		a249 = ((((a249 * 15) / 10) + 3262) + 23354);
		a269 = 35;
		a329 = 34;
		a207 = 35;
		a378 = 1;
		a243 = (((a243 + -16291) / 5) + -19355);
		a386 = (((a386 - 2329) + -6634) * 3);
		a265 = a376;
		a339 = 1;
		a336 = 0;
		a358 = a351;
		a302 = a346[2];
		a333 = (((((a333 + 9187) % 14) + 158) - -16080) - 16083);
		a307 = a227[3];
		a228 = a264;
		a75 = 32;
		a359 = 7;
		a211 = 6;
		a392 = a304;
		a202 = a217[4];
		a324 = a232[4];
		a277 = ((((a277 + -19310) + 3021) + 43939) - 56531);
		a172 = ((a158 + a237) - 2);
		a398 = 13;
		a206 = 6;
		a237 = 10;
	}
	if ((((((a324 == a232[2] && (a57 == 10 && (cf == 1 && a75 == 34))) && (92 == a296[2])) && a81 == a167[2]) && a230 == 5) && (((a158 == 4 && ((50 == a392[4]) && (47 == a239[4]))) && input == inputs[1]) && ((-57 < a357) && (20 >= a357))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if (((cf != 1 && (cf == 1 && a139 == 33)) || 493 < a130)) {
			a244 = a363[(a230 + -5)];
			a173 = 36;
			a75 = 32;
			a141 = a47[(a57 + -8)];
		} else {
			a173 = 33;
			a373 = 1;
			a211 = 8;
			a234 = a372[6];
			a202 = a217[5];
			a329 = 34;
			a265 = a303;
			a130 = (((28 / 5) + 25932) - -935);
			a313 = 35;
			a206 = 9;
			a338 = 6;
			a382 = (((((a382 % 107) - -69) + 14638) - -6632) + -21270);
			a237 = 10;
			a312 = 36;
			a392 = a304;
			a368 = 1;
			a357 = (((a357 + -8177) * 3) + -4389);
			a249 = ((((a249 - 27085) - 1228) - -40965) * -2);
			a386 = ((((a386 * 5) * 5) % 61) - -210);
			a302 = a346[6];
			a320 = 7;
			a336 = 0;
			a353 = a263;
			a75 = 32;
			a300 = 1;
			a270 = 12;
			a361 = 36;
			a243 = (((a243 - -28749) + -5533) - -2979);
			a378 = 1;
			a324 = a232[5];
			a218 = 35;
			a296 = a212;
			a240 = 1;
			a228 = a229;
			a239 = a242;
			a277 = (((a277 / 5) + 11300) - -17080);
			a339 = 1;
			a269 = 33;
			a398 = 14;
			a207 = 36;
			a370 = a311;
			a358 = a348;
			a333 = ((((a333 - 189) / 5) - -16539) + -16417);
			a230 = 3;
			a307 = a227[2];
			a359 = 7;
			a13 = (((((((a130 * a130) % 14999) / 5) + 20202) - -2683) % 60) - -241);
		}
	}
	if (((((148 < a277) && (339 >= a277)) && (((input == inputs[2] && a312 == 34) && a312 == 34) && a373 != 1)) && (a158 == 4 && (((((cf == 1 && a75 == 34) && a57 == 10) && (77 == a358[0])) && a313 == 34) && a81 == a167[2])))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a178 -= (a178 - 20) < a178 ? 2 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if ((!(a270 == 10) || (27 == a46[0]))) {
			a75 = 32;
			a173 = 32;
			a129 = a92[((a211 + a338) - 2)];
			a125 = a30[(a237 + 2)];
		} else {
			a136 = ((a320 / a359) - -11);
			a75 = 33;
			a132 = 0;
			a77 = ((a206 * a398) + -67);
		}
	}
}
void calculate_outputm104(int input) {
	if ((((((((-156 < a243) && (-68 >= a243)) && a218 == 34) && a57 == 10) && a320 == 8) && a240 == 1) && (((((148 < a277) && (339 >= a277)) && ((a75 == 34 && (input == inputs[7] && cf == 1)) && a158 == 5)) && a200 == a115[2]) && a211 == 3))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a35 += (a35 + 20) > a35 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		if ((a295 == 11 || (!(47 == a265[5]) || (!(a184 == 9) || ((77 == a195[1]) || !(a171 == 36)))))) {
			a357 = (((a357 / 5) - 17877) / 5);
			a358 = a335;
			a392 = a304;
			a173 = 35;
			a249 = ((((a249 + -25340) * 1) - 3643) + 47528);
			a240 = 1;
			a336 = 1;
			a234 = a372[7];
			a320 = 9;
			a276 = a250;
			a211 = 3;
			a313 = 35;
			a207 = 33;
			a237 = 7;
			a270 = 15;
			a382 = (((43 - -18490) - -5499) * 1);
			a302 = a346[7];
			a256 = 36;
			a91 = (a158 + 3);
			a361 = 34;
			a75 = 32;
			a310 = (((a310 / 5) / -5) + -14747);
			a338 = 5;
			a269 = 35;
			a218 = 34;
			a102 = a127[(a57 + -4)];
		} else {
			a302 = a346[5];
			a228 = a264;
			a235 = a216[6];
			a383 = a226[4];
			a218 = 32;
			a270 = 16;
			a339 = 0;
			a234 = a372[4];
			a286 = a294[1];
			a224 = 35;
			a295 = a366[(a338 + -3)];
			a296 = a212;
			a75 = 35;
			a359 = 9;
			a357 = (((a357 + -16834) / 5) * 5);
			a329 = 36;
			a225 = a205[2];
			a333 = (((a333 + -11339) + -14962) - -26268);
			a171 = 36;
			a358 = a351;
			a386 = ((((94 * 5) * 5) * 1) / 10);
			a312 = 34;
			a206 = 8;
			a382 = ((((16 * -41) / 10) * 5) - 18182);
			a373 = 1;
			a249 = ((((a249 * 15) / 10) / 5) * 5);
			a378 = 0;
			a260 = 1;
			a353 = a399;
			a392 = a304;
			a398 = 15;
			a368 = 1;
			a240 = 1;
			a230 = 7;
			a202 = a217[5];
			a320 = 10;
			a313 = 36;
			a277 = ((((((a277 * 23) / 10) * 10) / 9) - 16100) + 18285);
			a243 = (((a243 - 23668) + 34849) - -8712);
			a237 = 10;
			a324 = a232[1];
			a239 = a268;
			a201 = ((((a201 + 8044) * 3) * 10) / 9);
			a256 = 35;
			a395 = 0;
			a134 = 0;
			a207 = 32;
			a370 = a318;
			a310 = (((a310 / 5) - -255) - -14);
			a265 = a293;
			a336 = 0;
			a211 = 8;
			a361 = 34;
			a300 = 0;
			a307 = a227[2];
			a338 = 6;
		}
	}
	if (((a158 == 5 && (((input == inputs[3] && (a320 == 8 && ((355 < a249) && (499 >= a249)))) && a75 == 34) && a224 == 34)) && (((((a57 == 10 && cf == 1) && a200 == a115[2]) && a230 == 5) && a359 == 5) && ((-12 < a201) && (178 >= a201))))) {
		a120 += (a120 + 20) > a120 ? 2 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a313 = 34;
		a234 = a372[5];
		a300 = 1;
		a218 = 34;
		a382 = (((((49 - -12214) / 5) + -3511) * -2) / 10);
		a91 = (a237 + 3);
		a302 = a346[0];
		a75 = 32;
		a211 = 8;
		a338 = 6;
		a270 = 17;
		a370 = a318;
		a207 = 35;
		a276 = a253;
		a324 = a232[5];
		a359 = 3;
		a320 = 13;
		a395 = 1;
		a358 = a335;
		a102 = a127[((a230 + a57) - 10)];
		a357 = ((((a357 % 38) - 17) - 2) + 2);
		a392 = a208;
		a307 = a227[0];
		a368 = 1;
		a383 = a226[6];
		a378 = 1;
		a206 = 10;
		a265 = a303;
		a312 = 34;
		a336 = 1;
		a235 = a216[0];
		a256 = 35;
		a224 = 33;
		a228 = a292;
		a398 = 12;
		a240 = 1;
		a201 = ((((a201 / 5) - 21542) * 10) / 9);
		a286 = a294[4];
		a353 = a263;
		a249 = (((a249 - -19584) + 5915) + 1033);
		a339 = 1;
		a269 = 33;
		a310 = (((a310 * 5) * 5) * -3);
		a173 = 35;
		a230 = 8;
		a225 = a205[4];
		a329 = 35;
		a243 = (((a243 + 18038) + 11571) * 1);
		a237 = 6;
	}
	if (((((316 < a310) && (357 >= a310)) && (a338 == 5 && (a313 == 34 && ((cf == 1 && a57 == 10) && a158 == 5)))) && (((a75 == 34 && ((a256 == 34 && a359 == 5) && input == inputs[9])) && ((355 < a249) && (499 >= a249))) && a200 == a115[2]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a57 = (a158 - -7);
		a81 = a167[((a57 + a57) - 22)];
		a158 = (a57 - 4);
	}
	if (((a158 == 5 && ((a302 == a346[2] && ((-156 < a243) && (-68 >= a243))) && a300 == 1)) && (((((15 == a353[2]) && (((a75 == 34 && cf == 1) && a57 == 10) && a270 == 12)) && a324 == a232[2]) && a200 == a115[2]) && input == inputs[1]))) {
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a183 = 35;
		a278 = a326[a158];
		a57 = (a230 - -11);
	}
	if ((((a75 == 34 && ((47 == a239[4]) && (15 == a353[2]))) && a368 == 1) && ((((input == inputs[2] && (a57 == 10 && (a158 == 5 && (a200 == a115[2] && cf == 1)))) && (47 == a239[4])) && a237 == 5) && (77 == a358[0])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a178 -= (a178 - 20) < a178 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a75 = 35;
		a196 = (a320 + 2);
		a134 = 1;
		a129 = a92[(a196 - 3)];
	}
	if (((a307 == a227[2] && ((a359 == 5 && a359 == 5) && a359 == 5)) && (((((a57 == 10 && ((a75 == 34 && cf == 1) && a158 == 5)) && a270 == 12) && a200 == a115[2]) && (77 == a358[0])) && input == inputs[6]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		a168 += (a168 + 20) > a168 ? 2 : 0;
		cf = 0;
		a57 = ((a338 / a398) - -15);
		a72 = (((((90 + -10021) / 5) / 5) * -7) / 10);
		a17 = ((((((a72 * a72) % 14999) / 5) + 26465) + -12364) - 22568);
	}
	if (((a225 == a205[2] && ((input == inputs[0] && ((cf == 1 && a200 == a115[2]) && a57 == 10)) && a378 == 1)) && (a324 == a232[2] && ((a75 == 34 && (a361 == 34 && (((147 < a333) && (177 >= a333)) && a158 == 5))) && a202 == a217[2])))) {
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a174 += (a174 + 20) > a174 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		cf = 0;
		a46 = a148;
		a75 = 36;
		a146 = 1;
		a72 = ((((64 + 5194) - -3211) * 10) / 9);
	}
	if (((a324 == a232[2] && (a211 == 3 && (a329 == 34 && a324 == a232[2]))) && (input == inputs[5] && (a158 == 5 && (((a336 == 1 && ((cf == 1 && a57 == 10) && a75 == 34)) && a200 == a115[2]) && ((-156 < a243) && (-68 >= a243))))))) {
		a120 -= (a120 - 20) < a120 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a57 = (a158 + 10);
		a141 = a47[a158];
		a72 = (((74 - 28981) + -796) - 126);
	}
	if (((((59 == a228[3]) && ((input == inputs[8] && (a57 == 10 && (cf == 1 && a75 == 34))) && a225 == a205[2])) && a206 == 6) && ((((a383 == a226[2] && a200 == a115[2]) && a158 == 5) && a313 == 34) && a256 == 34))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 1 : 0;
		a174 += (a174 + 20) > a174 ? 4 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		if ((a243 <= -179 && ((a260 != 1 || a398 == 13) || a320 == 9))) {
			a361 = 34;
			a398 = 16;
			a265 = a376;
			a277 = ((((a277 - 9185) * 3) + -149) + 43597);
			a173 = 33;
			a243 = ((((a243 % 43) + -90) * 5) / 5);
			a333 = ((((a333 % 14) + 158) + 27214) - 27223);
			a358 = a335;
			a353 = a399;
			a130 = (((29 - -17158) * 1) * 1);
			a211 = 5;
			a382 = (((1 - 8228) - 15208) - 6289);
			a286 = a294[6];
			a300 = 1;
			a336 = 0;
			a359 = 9;
			a313 = 33;
			a373 = 1;
			a206 = 9;
			a224 = 34;
			a312 = 36;
			a237 = 8;
			a378 = 1;
			a329 = 36;
			a228 = a229;
			a75 = 32;
			a270 = 10;
			a357 = (((a357 + 7074) - -12920) + 5493);
			a276 = a250;
			a368 = 1;
			a240 = 1;
			a392 = a304;
			a218 = 34;
			a370 = a311;
			a310 = (((a310 + -23277) - 5279) + -1713);
			a230 = 3;
			a302 = a346[7];
			a269 = 35;
			a202 = a217[3];
			a339 = 1;
			a338 = 3;
			a234 = a372[3];
			a201 = (((a201 - 6972) + -12610) * 1);
			a207 = 33;
			a324 = a232[7];
			a235 = a216[7];
			a307 = a227[0];
			a296 = a362;
			a320 = 7;
			a239 = a242;
			a249 = ((((a249 + 5738) * 4) * 10) / 9);
			a13 = (((((((a130 * a130) % 14999) - -6013) % 60) + 251) - 28815) - -28801);
		} else {
			a243 = (((((a243 % 11) + -165) / 5) * 10) / 2);
			a211 = 5;
			a336 = 0;
			a75 = 35;
			a312 = 33;
			a239 = a268;
			a310 = ((((((a310 * 5) % 20) + 328) * 5) % 20) + 323);
			a202 = a217[4];
			a339 = 0;
			a361 = 36;
			a357 = (((a357 * 5) + -18686) * 1);
			a392 = a304;
			a235 = a216[2];
			a224 = 33;
			a353 = a263;
			a218 = 36;
			a270 = 14;
			a207 = 34;
			a333 = (((((a333 * -1) / 10) + 4) * 10) / 9);
			a338 = 7;
			a237 = 6;
			a201 = (((a201 + 7728) * 3) * 1);
			a134 = 1;
			a359 = 8;
			a135 = 33;
			a368 = 0;
			a398 = 15;
			a329 = 36;
			a320 = 8;
			a230 = 10;
			a256 = 34;
			a277 = (((a277 / 5) + -15240) - 6797);
			a395 = 1;
			a378 = 0;
			a324 = a232[4];
			a373 = 0;
			a313 = 36;
			a260 = 1;
			a386 = (((43 * 5) * -5) * 5);
			a307 = a227[4];
			a358 = a351;
			a296 = a384;
			a225 = a205[5];
			a240 = 0;
			a249 = (((((a249 * 15) / 10) / 5) * 10) / 2);
			a206 = 10;
			a269 = 32;
			a300 = 0;
			a370 = a311;
			a228 = a264;
			a196 = (a158 + 10);
		}
	}
	if (((a302 == a346[2] && a202 == a217[2]) && (a398 == 12 && (a312 == 34 && (a302 == a346[2] && ((a158 == 5 && (a57 == 10 && (a307 == a227[2] && ((cf == 1 && a75 == 34) && a200 == a115[2])))) && input == inputs[4])))))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 1 : 0;
		cf = 0;
		if (((23 == a274[2]) && a339 == 1)) {
			a225 = a205[0];
			a265 = a303;
			a286 = a294[0];
			a320 = 13;
			a57 = (a270 + 1);
			a395 = 1;
			a260 = 0;
			a296 = a384;
			a370 = a311;
			a382 = (((52 - -3736) / 5) * 5);
			a361 = 34;
			a323 = (a211 - -4);
			a312 = 34;
			a202 = a217[2];
			a235 = a216[6];
			a269 = 36;
			a324 = a232[6];
			a302 = a346[5];
			a276 = a253;
			a386 = ((((((46 * 10) / 1) + -14206) - -4412) * -1) / 10);
			a234 = a372[4];
			a137 = a117;
		} else {
			a276 = a250;
			a225 = a205[0];
			a339 = 0;
			a224 = 35;
			a202 = a217[5];
			a239 = a242;
			a302 = a346[5];
			a310 = (((((a310 * 12) / 10) + -23759) * -1) / 10);
			a207 = 33;
			a237 = 5;
			a75 = 32;
			a320 = 10;
			a392 = a304;
			a172 = (a57 - 9);
			a395 = 1;
			a313 = 34;
			a234 = a372[5];
			a270 = 12;
			a378 = 1;
			a218 = 35;
			a300 = 1;
			a370 = a311;
			a373 = 1;
			a296 = a362;
			a336 = 1;
			a368 = 1;
			a265 = a376;
			a383 = a226[4];
			a357 = ((((a357 * 5) + 7045) * 10) / 9);
			a382 = ((((2 * 5) + -38) * 5) - -212);
			a358 = a348;
			a286 = a294[5];
			a338 = 5;
			a256 = 36;
			a235 = a216[4];
			a173 = 34;
			a361 = 35;
			a398 = 17;
			a277 = ((((((a277 * 10) / 4) + 21337) - 24879) * -2) / 10);
			a230 = 7;
			a240 = 1;
			a312 = 33;
			a324 = a232[0];
			a228 = a229;
			a201 = ((((a201 + 8056) * 3) + 4261) + -30177);
			a329 = 34;
			a333 = (((a333 + 457) - -21469) * 1);
			a307 = a227[0];
			a249 = ((((a249 * -5) - 18955) + 43035) + -30265);
			a129 = a92[((a359 * a172) - -2)];
			a206 = 9;
			a359 = 3;
		}
	}
}
void calculate_outputm105(int input) {
	if ((((a361 == 34 && (a200 == a115[5] && ((92 == a296[2]) && ((input == inputs[3] && cf == 1) && a158 == 5)))) && ((92 == a296[2]) && ((((a312 == 34 && a313 == 34) && a75 == 34) && ((201 < a386) && (325 >= a386))) && a57 == 10))) && a161 >= 5)) {
		cf = 0;
		a105 = 36;
		a158 = (a57 - 4);
	}
	if (((((((((-39 < a382) && (176 >= a382)) && (a312 == 34 && ((cf == 1 && a75 == 34) && a200 == a115[5]))) && a158 == 5) && a395 == 1) && a57 == 10) && (((a336 == 1 && a240 == 1) && a260 == 1) && input == inputs[1])) && (a93 % 2 == 0))) {
		cf = 0;
		a129 = a92[a338];
		a75 = 33;
		a132 = 0;
		a77 = (a57 + 2);
	}
	if (((((a269 == 34 && ((((cf == 1 && a158 == 5) && a57 == 10) && (56 == a265[2])) && a368 == 1)) && a234 == a372[2]) && ((input == inputs[5] && (a200 == a115[5] && (((-57 < a357) && (20 >= a357)) && a75 == 34))) && a368 == 1)) && a94 <= 3)) {
		cf = 0;
		a368 = 1;
		a230 = (a206 - 3);
		a99 = a26[((a398 / a237) - -1)];
		a260 = 1;
		a202 = a217[(a57 + -10)];
		a201 = ((((((a201 * a277) % 14999) + -14160) % 14900) + -15098) + -3);
		a269 = 33;
		a358 = a348;
		a353 = a263;
		a75 = 33;
		a320 = (a230 + 3);
		a224 = 33;
		a218 = 33;
		a77 = ((a211 - a158) - -13);
		a243 = ((((((a243 * a386) % 14999) + -1561) * 10) / 9) * 1);
		a359 = (a338 - 2);
		a239 = a242;
		a211 = (a57 - 9);
		a132 = 0;
		a310 = (((((a333 * a333) % 14999) + -29473) - 469) + -55);
		a324 = a232[(a320 + -6)];
	}
	if (((((92 == a296[2]) && (a286 == a294[2] && (a75 == 34 && (a200 == a115[5] && ((a207 == 34 && a361 == 34) && a57 == 10))))) && ((a398 == 12 && (input == inputs[7] && (cf == 1 && a158 == 5))) && a202 == a217[2])) && (a156 % 2 == 0))) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		cf = 0;
		a77 = ((a230 - a359) + 10);
		a75 = 33;
		a132 = 0;
		a1 = a87[((a206 + a359) + -8)];
	}
	if ((((((a57 == 10 && (a234 == a372[2] && (((cf == 1 && a158 == 5) && input == inputs[2]) && (92 == a296[2])))) && a361 == 34) && a383 == a226[2]) && ((a75 == 34 && (a200 == a115[5] && ((147 < a333) && (177 >= a333)))) && a218 == 34)) && a181 == 1220)) {
		a31 += (a31 + 20) > a31 ? 1 : 0;
		cf = 0;
		a143 = 35;
		a210 = 1;
		a57 = (a206 + 5);
	}
	if (((((a329 == 34 && (((92 == a296[2]) && ((a158 == 5 && cf == 1) && a75 == 34)) && (77 == a358[0]))) && input == inputs[8]) && ((((a200 == a115[5] && a202 == a217[2]) && a57 == 10) && a237 == 5) && ((-12 < a201) && (178 >= a201)))) && a31 <= -3)) {
		a67 -= (a67 - 20) < a67 ? 2 : 0;
		cf = 0;
		a158 = (a57 + -2);
		a81 = a167[((a320 + a237) + -11)];
		a57 = (a230 + 7);
	}
	if (((((77 == a358[0]) && ((92 == a296[2]) && (a75 == 34 && (a57 == 10 && (a398 == 12 && (a158 == 5 && (cf == 1 && a200 == a115[5]))))))) && (a206 == 6 && (((50 == a392[4]) && input == inputs[9]) && a339 != 1))) && a51 <= 3)) {
		a169 -= (a169 - 20) < a169 ? 3 : 0;
		cf = 0;
		a278 = a326[((a206 + a359) + -9)];
		a40 = a65;
		a57 = ((a338 * a320) - 24);
	}
	if ((((((-156 < a243) && (-68 >= a243)) && ((a312 == 34 && a57 == 10) && a256 == 34)) && (a302 == a346[2] && ((((a336 == 1 && (input == inputs[4] && (cf == 1 && a158 == 5))) && a200 == a115[5]) && a75 == 34) && a373 != 1))) && (a88 % 2 == 0))) {
		a178 += (a178 + 20) > a178 ? 4 : 0;
		cf = 0;
		a73 = (((((a277 * a386) % 14999) - 15840) * 1) - 2194);
		a146 = 0;
		a75 = 36;
		a39 = a144;
	}
	if (((a270 == 12 && (a158 == 5 && (((a200 == a115[5] && ((input == inputs[6] && (cf == 1 && a75 == 34)) && ((355 < a249) && (499 >= a249)))) && a373 != 1) && (47 == a239[4])))) && ((a300 == 1 && a237 == 5) && a57 == 10))) {
		a162 += (a162 + 20) > a162 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 2 : 0;
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		cf = 0;
		a386 = ((((((a386 * a243) % 14999) % 61) + 139) / 5) + 95);
		a249 = (((((((a249 * a277) % 14999) / 5) / 5) - -28808) % 101) - -196);
		a370 = a285;
		a378 = 0;
		a234 = a372[(a338 - 5)];
		a240 = 0;
		a368 = 0;
		a225 = a205[((a338 - a338) - -1)];
		a358 = a348;
		a312 = 32;
		a237 = ((a398 - a206) - 2);
		a382 = ((((((((a382 * a201) % 14999) % 12) + -52) - -1) * 5) % 12) - 43);
		a302 = a346[(a338 - 4)];
		a270 = (a158 - -6);
		a207 = 32;
		a336 = 0;
		a269 = 32;
		a353 = a241;
		a206 = a338;
		a357 = (((((a357 * a333) / 5) % 65) + -121) + -1);
		a224 = 32;
		a235 = a216[((a338 + a338) - 9)];
		a361 = 32;
		a218 = 32;
		a395 = 0;
		a307 = a227[(a237 - 3)];
		a329 = 32;
		a286 = a294[(a270 - 10)];
		a75 = 32;
		a129 = a92[(a320 - 7)];
		a211 = (a338 + -4);
		a172 = (a57 - 9);
		a313 = 32;
		a256 = 32;
		a276 = a289;
		a265 = a293;
		a320 = (a158 + 2);
		a359 = (a338 - 1);
		a333 = ((((((((a201 * a201) % 14999) / 5) % 96) + 51) * 5) % 96) + 51);
		a296 = a384;
		a260 = 0;
		a339 = 0;
		a373 = 1;
		a202 = a217[((a338 * a398) - 60)];
		a230 = (a338 - 1);
		a300 = 0;
		a310 = (((((((a243 * a386) % 14999) % 77) + 238) / 5) / 5) + 165);
		a398 = (a338 - -6);
		a392 = a257;
		a201 = (((((((a201 * a243) % 93) - 105) - 1) * 5) % 93) - 104);
		a243 = ((((((a243 * a310) % 14999) + 3397) + -1852) % 11) + -167);
		a173 = 34;
		a338 = a230;
	}
}
void calculate_outputm107(int input) {
	if ((((77 == a358[0]) && (a200 == a115[7] && (a75 == 34 && (a158 == 5 && (cf == 1 && input == inputs[6]))))) && (a202 == a217[2] && (a338 == 5 && ((((201 < a386) && (325 >= a386)) && (((148 < a277) && (339 >= a277)) && a234 == a372[2])) && a57 == 10))))) {
		a169 -= (a169 - 20) < a169 ? 4 : 0;
		cf = 0;
		a353 = a263;
		a237 = ((a320 + a320) - 11);
		a277 = ((((((((a386 * a310) % 14999) / 5) % 78) - -61) * 5) % 78) + 11);
		a260 = 0;
		a75 = 32;
		a218 = 33;
		a234 = a372[((a398 * a57) + -120)];
		a207 = 32;
		a357 = (((((((a277 * a310) % 14999) * 2) - -1) + 0) % 65) - 121);
		a239 = a242;
		a333 = ((((((a310 * a277) % 14999) + -2122) % 14976) - 15022) * 1);
		a201 = (((((((a201 * a357) % 14999) * 2) * 1) * 1) % 93) + -104);
		a228 = a229;
		a256 = 32;
		a395 = 0;
		a42 = (a57 + -2);
		a300 = 1;
		a359 = ((a338 - a206) - -4);
		a240 = 0;
		a383 = a226[(a398 - 12)];
		a386 = ((((((a386 * a277) % 14999) % 61) - -138) - -2745) - 2742);
		a324 = a232[(a206 - 5)];
		a398 = a57;
		a141 = a47[(a206 - 5)];
		a312 = 33;
		a225 = a205[(a338 + -5)];
		a173 = 36;
		a307 = a227[(a270 - 10)];
		a373 = 1;
		a211 = (a158 + -4);
		a230 = ((a158 - a158) - -3);
		a206 = a338;
		a338 = ((a320 + a320) + -11);
	}
}
void calculate_outputm108(int input) {
	if (((a359 == 5 && (a307 == a227[2] && ((a158 == 6 && (a57 == 10 && cf == 1)) && a75 == 34))) && (((a105 == 34 && (((77 == a358[0]) && input == inputs[0]) && a329 == 34)) && (92 == a296[2])) && a339 != 1))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		cf = 0;
		a302 = a346[((a230 + a230) + -6)];
		a75 = 36;
		a357 = ((((a357 * a310) - 8623) * 1) + -1273);
		a338 = (a398 / a230);
		a395 = 1;
		a218 = 33;
		a339 = 1;
		a146 = 0;
		a296 = a212;
		a237 = a338;
		a240 = 1;
		a64 = 0;
		a73 = (((46 + 10432) / 5) / 5);
	}
	if (((((((a313 == 34 && ((316 < a310) && (357 >= a310))) && a368 == 1) && a225 == a205[2]) && input == inputs[4]) && a57 == 10) && ((((a105 == 34 && (a75 == 34 && cf == 1)) && ((-57 < a357) && (20 >= a357))) && a336 == 1) && a158 == 6))) {
		a178 -= (a178 - 20) < a178 ? 1 : 0;
		cf = 0;
		a313 = 32;
		a307 = a227[(a158 + -5)];
		a240 = 1;
		a237 = ((a57 + a57) - 17);
		a265 = a376;
		a329 = 33;
		a276 = a250;
		a207 = 33;
		a286 = a294[(a158 + -4)];
		a249 = ((((((a386 * a386) % 14999) - 2334) * 1) % 71) + 427);
		a357 = (((((a357 * a386) % 14999) / 5) - 19419) * 1);
		a300 = 1;
		a73 = ((((16 + 23698) + -23503) - -13235) - 13255);
		a358 = a348;
		a353 = a263;
		a146 = 0;
		a382 = ((((((((a382 * a333) % 14999) % 12) - 50) * 1) * 5) % 12) + -43);
		a395 = 1;
		a224 = 34;
		a336 = 1;
		a234 = a372[(a158 + -4)];
		a202 = a217[(a359 + -4)];
		a310 = ((((((a310 * a277) % 14999) - -19206) + 9876) % 77) - -212);
		a338 = ((a158 + a206) - 9);
		a218 = 33;
		a75 = 36;
		a16 = 1;
		a320 = (a359 - -2);
		a339 = 1;
		a368 = 1;
		a383 = a226[((a398 * a398) + -100)];
		a225 = a205[((a206 + a230) - 9)];
		a256 = 34;
		a302 = a346[(a158 + -4)];
		a206 = (a359 + -1);
		a296 = a212;
		a359 = (a230 + 2);
	}
}
void calculate_outputm113(int input) {
	if (((a237 == 5 && (a383 == a226[2] && (a75 == 34 && ((cf == 1 && a57 == 10) && a81 == a167[5])))) && (input == inputs[6] && ((a158 == 8 && ((a378 == 1 && a336 == 1) && a307 == a227[2])) && ((-156 < a243) && (-68 >= a243)))))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		cf = 0;

	}
}
void calculate_outputm115(int input) {
	if (((((-39 < a382) && (176 >= a382)) && (a57 == 10 && (a240 == 1 && ((a383 == a226[2] && a302 == a346[2]) && (56 == a265[2]))))) && ((59 == a228[3]) && (((a158 == 11 && (a75 == 34 && cf == 1)) && input == inputs[4]) && a155 == 36)))) {
		a165 += (a165 + 20) > a165 ? 4 : 0;
		a98 += (a98 + 20) > a98 ? 6 : 0;
		a174 += (a174 + 20) > a174 ? 4 : 0;
		cf = 0;
		a302 = a346[(a57 + -9)];
		a8 = ((a359 - a270) - -17);
		a240 = 0;
		a277 = (((((((a310 * a310) % 14999) + 14212) + -29297) * 1) % 78) + 113);
		a329 = 34;
		a173 = 32;
		a333 = (((((a249 * a249) % 14999) + -28199) / 5) - 9931);
		a286 = a294[(a237 - 2)];
		a225 = a205[(a398 - a57)];
		a224 = 32;
		a370 = a285;
		a228 = a264;
		a243 = (((((a243 * a277) % 11) + -166) * 1) - 1);
		a320 = ((a57 * a398) + -103);
		a125 = a30[(a158 - 10)];
		a211 = (a398 - 10);
		a307 = a227[(a206 + -4)];
		a382 = ((((((a382 * a201) % 14999) % 12) - 51) + -18636) + 18636);
		a338 = (a8 + -6);
		a358 = a351;
		a234 = a372[(a398 - 11)];
		a386 = ((((((a386 * a357) % 61) - -138) * 1) + 4508) - 4507);
		a336 = 1;
		a260 = 0;
		a357 = (((((a357 * a310) * 1) % 65) - 121) - 2);
		a202 = a217[((a398 + a237) + -15)];
		a270 = ((a237 + a230) + 3);
		a353 = a241;
		a373 = 0;
		a75 = 32;
		a359 = (a398 + -7);
	}
	if ((((a75 == 34 && (((77 == a358[0]) && a373 != 1) && ((201 < a386) && (325 >= a386)))) && a218 == 34) && ((a158 == 11 && (a155 == 36 && (a359 == 5 && (a57 == 10 && (input == inputs[3] && cf == 1))))) && ((-156 < a243) && (-68 >= a243))))) {
		cf = 0;
		a211 = (a158 + -9);
		a75 = 32;
		a173 = 32;
		a225 = a205[(a359 + -5)];
		a218 = 32;
		a270 = a398;
		a228 = a229;
		a256 = 32;
		a260 = 0;
		a300 = 0;
		a302 = a346[(a237 - 3)];
		a361 = 32;
		a240 = 0;
		a357 = (((((a357 * a310) * 1) % 65) - 121) + -1);
		a383 = a226[(a320 - a320)];
		a382 = ((((((a382 * a357) % 14999) % 12) + -50) + 18515) + -18516);
		a358 = a351;
		a307 = a227[(a158 - 10)];
		a243 = (((((((a249 * a386) % 14999) - -604) - -6258) / 5) % 11) + -175);
		a338 = ((a230 / a230) + 3);
		a265 = a293;
		a207 = 32;
		a373 = 0;
		a359 = (a211 + 2);
		a320 = ((a206 - a359) + 6);
		a395 = 0;
		a370 = a285;
		a386 = ((((((a386 * a243) % 14999) - 11300) - 1625) % 61) - -186);
		a125 = a30[(a57 + -10)];
		a239 = a299;
		a54 = ((((87 * 5) * 5) * 10) / 9);
	}
}
void calculate_outputm8(int input) {
	if (((((147 < a333) && (177 >= a333)) && (a378 == 1 && ((50 == a392[4]) && (38 == a370[4])))) && (((cf == 1 && a158 == 4) && (59 == a228[3])) && ((-156 < a243) && (-68 >= a243))))) {
		if ((((92 == a296[2]) && (((a361 == 34 && a269 == 34) && a361 == 34) && (92 == a296[2]))) && ((cf == 1 && a81 == a167[2]) && a202 == a217[2]))) {
			calculate_outputm102(input);
		}
	}
	if (((((a158 == 5 && cf == 1) && a256 == 34) && a324 == a232[2]) && (((((-57 < a357) && (20 >= a357)) && a339 != 1) && a207 == 34) && (47 == a239[4])))) {
		if (((a235 == a216[2] && ((47 == a239[4]) && (a200 == a115[2] && cf == 1))) && (((a373 != 1 && a359 == 5) && a240 == 1) && (47 == a239[4])))) {
			calculate_outputm104(input);
		}
		if ((((a211 == 3 && (a339 != 1 && (a359 == 5 && a312 == 34))) && a286 == a294[2]) && ((77 == a358[0]) && (a200 == a115[5] && cf == 1)))) {
			calculate_outputm105(input);
		}
		if ((((a395 == 1 && (cf == 1 && a200 == a115[7])) && ((-12 < a201) && (178 >= a201))) && ((a260 == 1 && (a398 == 12 && a307 == a227[2])) && a235 == a216[2]))) {
			calculate_outputm107(input);
		}
	}
	if ((((a206 == 6 && a320 == 8) && (15 == a353[2])) && ((((a158 == 6 && cf == 1) && a313 == 34) && a256 == 34) && a313 == 34))) {
		if (((((-39 < a382) && (176 >= a382)) && (a302 == a346[2] && (a105 == 34 && cf == 1))) && (((a320 == 8 && a237 == 5) && a395 == 1) && a313 == 34))) {
			calculate_outputm108(input);
		}
	}
	if (((((((-12 < a201) && (178 >= a201)) && (56 == a265[2])) && a235 == a216[2]) && a230 == 5) && (((cf == 1 && a158 == 8) && a202 == a217[2]) && (56 == a265[2])))) {
		if (((a373 != 1 && ((cf == 1 && a81 == a167[5]) && (47 == a239[4]))) && (a378 == 1 && ((((-39 < a382) && (176 >= a382)) && a260 == 1) && a324 == a232[2])))) {
			calculate_outputm113(input);
		}
	}
	if (((((38 == a370[4]) && a300 == 1) && (47 == a239[4])) && ((((a158 == 11 && cf == 1) && a373 != 1) && (47 == a239[4])) && (59 == a228[3])))) {
		if (((((201 < a386) && (325 >= a386)) && a260 == 1) && ((a256 == 34 && ((56 == a265[2]) && (a338 == 5 && (cf == 1 && a155 == 36)))) && a320 == 8))) {
			calculate_outputm115(input);
		}
	}
}
void calculate_outputm116(int input) {
	if (((((148 < a277) && (339 >= a277)) && ((a75 == 34 && (input == inputs[1] && cf == 1)) && a57 == 11)) && (((316 < a310) && (357 >= a310)) && (a218 == 34 && (a256 == 34 && (a302 == a346[2] && (a143 == 32 && (((-12 < a201) && (178 >= a201)) && a14 == a79[2])))))))) {
		cf = 0;
		a270 = ((a359 + a230) + 1);
		a312 = 32;
		a75 = 32;
		a218 = 32;
		a338 = (a57 + -7);
		a172 = (a237 + -1);
		a240 = 0;
		a357 = (((((a357 * a243) % 65) + -122) * 1) * 1);
		a224 = 32;
		a302 = a346[(a359 - 4)];
		a173 = 34;
		a392 = a257;
		a310 = (((((((a310 * a243) % 14999) % 77) + 238) + 2) + 29314) + -29316);
		a320 = ((a206 / a270) + 7);
		a274 = a290;
	}
	if (((((a359 == 5 && ((-156 < a243) && (-68 >= a243))) && a235 == a216[2]) && (77 == a358[0])) && ((a361 == 34 && (a143 == 32 && ((((a75 == 34 && cf == 1) && a57 == 11) && input == inputs[9]) && (50 == a392[4])))) && a14 == a79[2]))) {
		a67 += (a67 + 20) > a67 ? 1 : 0;
		cf = 0;
		a235 = a216[((a230 + a211) + -6)];
		a173 = 32;
		a125 = a30[(a206 - -1)];
		a382 = (((((a382 * a357) % 12) - 51) - -1) + -3);
		a357 = (((((a357 * a243) * 3) - 508) % 65) - 121);
		a320 = ((a338 / a338) + 6);
		a129 = a92[(a270 - 5)];
		a270 = (a230 - -6);
		a361 = 32;
		a392 = a257;
		a338 = (a206 + -2);
		a276 = a289;
		a368 = 1;
		a201 = (((((((a201 * a277) % 14999) - -2340) * 1) + 9250) % 93) - 104);
		a359 = (a57 - 7);
		a240 = 0;
		a312 = 32;
		a310 = (((((((a310 * a277) % 14999) + 1478) - 10320) / 5) % 77) - -237);
		a224 = 32;
		a277 = (((((((a277 * a310) % 14999) % 78) - 2) - 3) - 21339) - -21353);
		a230 = (a237 - 1);
		a206 = a237;
		a75 = 32;
		a237 = (a211 * a211);
	}
}
void calculate_outputm118(int input) {
	if ((((a320 == 8 && (a57 == 11 && (cf == 1 && a75 == 34))) && input == inputs[6]) && (((a398 == 12 && (a173 == 33 && ((a378 == 1 && a361 == 34) && a143 == 34))) && a361 == 34) && (56 == a265[2])))) {
		a164 -= (a164 - 20) < a164 ? 4 : 0;
		a168 += (a168 + 20) > a168 ? 2 : 0;
		cf = 0;
		a361 = 33;
		a333 = ((((((a333 * a382) % 14999) * 2) % 14976) - 15022) * 1);
		a320 = (a338 + a359);
		a353 = a241;
		a234 = a372[((a57 / a320) + -1)];
		a201 = (((((a201 * a357) - 5843) / 5) % 93) - 66);
		a265 = a303;
		a240 = 1;
		a382 = (((((((a357 * a249) % 14999) - -9254) % 14967) - 15031) - -23443) - 23443);
		a196 = (a270 - -3);
		a134 = 1;
		a307 = a227[(a237 - 2)];
		a75 = 35;
		a135 = 34;
		a260 = 0;
		a398 = (a237 - -8);
		a218 = 33;
		a324 = a232[((a57 - a320) + -4)];
		a230 = (a57 - 7);
		a270 = (a338 - -8);
		a373 = 1;
		a357 = ((((((a357 * a249) % 14999) - -3000) % 65) + -121) + -2);
	}
}
void calculate_outputm9(int input) {
	if ((((a230 == 5 && ((a240 == 1 && (cf == 1 && a143 == 32)) && a312 == 34)) && a359 == 5) && (a202 == a217[2] && a338 == 5))) {
		if (((a224 == 34 && (((cf == 1 && a14 == a79[2]) && a320 == 8) && a240 == 1)) && ((a206 == 6 && (47 == a239[4])) && (110 == a276[2])))) {
			calculate_outputm116(input);
		}
	}
	if ((((cf == 1 && a143 == 34) && a260 == 1) && ((77 == a358[0]) && (a373 != 1 && (a300 == 1 && ((15 == a353[2]) && a307 == a227[2])))))) {
		if ((((a173 == 33 && cf == 1) && (56 == a265[2])) && (((147 < a333) && (177 >= a333)) && (((a202 == a217[2] && a324 == a232[2]) && a234 == a372[2]) && (56 == a265[2]))))) {
			calculate_outputm118(input);
		}
	}
}
void calculate_outputm128(int input) {
	if ((((input == inputs[2] && (a81 == a167[2] && ((110 == a276[2]) && ((148 < a277) && (339 >= a277))))) && a313 == 34) && (a398 == 12 && (a158 == 4 && ((((-156 < a243) && (-68 >= a243)) && ((cf == 1 && a57 == 12) && a75 == 34)) && a218 == 34))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if ((((a307 == 5 || a132 == 1) || ((-188 < a357) && (-57 >= a357))) && !(a206 == 10))) {
			a72 = (((5 + -14540) - 7389) - -2361);
			a57 = (a206 - -9);
			a141 = a47[(a270 + -7)];
		} else {
			a329 = 35;
			a225 = a205[3];
			a398 = 13;
			a310 = (((((a310 * 12) / 10) * 10) / 9) - -7738);
			a370 = a311;
			a359 = 10;
			a224 = 36;
			a141 = a47[(a158 + -1)];
			a312 = 35;
			a358 = a351;
			a202 = a217[4];
			a386 = ((((a386 - 531) + -22269) * -1) / 10);
			a383 = a226[2];
			a57 = (a270 + 3);
			a239 = a268;
			a277 = (((a277 + -26840) + -243) - -43536);
			a72 = (((82 - 7497) * 4) - 246);
		}
	}
	if ((((((38 == a370[4]) && (a158 == 4 && ((59 == a228[3]) && input == inputs[3]))) && a207 == 34) && ((147 < a333) && (177 >= a333))) && ((15 == a353[2]) && (a202 == a217[2] && ((a81 == a167[2] && (a57 == 12 && cf == 1)) && a75 == 34))))) {
		a122 -= (a122 - 20) < a122 ? 4 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		cf = 0;
		if (((a125 == 5 && (((82 < a170) && (121 >= a170)) && !(a191 == 8))) || (26 == a137[1]))) {
			a72 = (((((a382 * a243) % 14948) + -15051) + 12910) + -12910);
			a57 = (a158 + 11);
			a141 = a47[(a270 + -5)];
		} else {
			a237 = 7;
			a370 = a318;
			a276 = a289;
			a228 = a292;
			a173 = 33;
			a392 = a208;
			a359 = 7;
			a353 = a399;
			a239 = a268;
			a361 = 33;
			a357 = (((a357 - 16778) + -2204) - 544);
			a398 = 17;
			a313 = 34;
			a383 = a226[6];
			a329 = 36;
			a202 = a217[3];
			a270 = 15;
			a249 = (((((a249 % 71) + 384) + 17360) - 14917) - 2415);
			a265 = a376;
			a277 = (((a277 + -28407) + -1250) - 120);
			a211 = 1;
			a206 = 4;
			a75 = 32;
			a234 = a372[7];
			a302 = a346[3];
			a373 = 0;
			a218 = 35;
			a368 = 1;
			a269 = 36;
			a130 = (((74 - -7467) + -14840) * 4);
			a224 = 34;
			a310 = ((((a310 + 23163) * 10) / 9) - -2154);
			a312 = 33;
			a386 = ((((a386 * 5) % 61) - -236) + -29);
			a300 = 1;
			a320 = 9;
			a243 = (((a243 - 14915) * 1) - 2051);
			a256 = 36;
			a307 = a227[0];
			a296 = a362;
			a235 = a216[3];
			a201 = (((((a201 - -6305) % 94) - -44) - -3312) + -3315);
			a240 = 1;
			a333 = ((((a333 * 10) / -9) - 26275) * 1);
			a382 = (((a382 + -4013) + -1440) / 5);
			a225 = a205[6];
			a358 = a335;
			a336 = 0;
			a339 = 1;
			a191 = a37[((a338 - a230) + 6)];
			a378 = 1;
			a207 = 36;
			a230 = 8;
			a324 = a232[2];
			a338 = 8;
		}
	}
	if (((a158 == 4 && ((((a225 == a205[2] && ((input == inputs[7] && cf == 1) && a81 == a167[2])) && a329 == 34) && a312 == 34) && ((-156 < a243) && (-68 >= a243)))) && ((a75 == 34 && (a237 == 5 && a237 == 5)) && a57 == 12))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a178 += (a178 + 20) > a178 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a132 = 0;
		a75 = 33;
		a136 = ((a158 / a57) + 5);
		a77 = a359;
	}
	if ((((a313 == 34 && ((((cf == 1 && a81 == a167[2]) && a158 == 4) && a75 == 34) && ((-156 < a243) && (-68 >= a243)))) && a312 == 34) && (a234 == a372[2] && ((input == inputs[6] && (a398 == 12 && (92 == a296[2]))) && a57 == 12)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if ((45 == a228[1])) {
			a179 = ((((((((a243 * a386) % 14999) % 40) - 16) + -2) * 5) % 40) + -17);
			a81 = a167[((a270 / a57) - -3)];
		} else {
			a202 = a217[7];
			a336 = 0;
			a206 = 10;
			a324 = a232[3];
			a243 = (((a243 + -6565) + -20100) - -42616);
			a302 = a346[3];
			a320 = 10;
			a386 = (((a386 - 3009) + 26681) * 1);
			a234 = a372[4];
			a75 = 36;
			a286 = a294[2];
			a329 = 35;
			a307 = a227[6];
			a353 = a399;
			a235 = a216[1];
			a249 = (((a249 / 5) - 4132) + 18934);
			a277 = ((((a277 * 23) / 10) * 5) - -12882);
			a218 = 35;
			a270 = 12;
			a237 = 9;
			a265 = a376;
			a361 = 35;
			a296 = a212;
			a370 = a311;
			a239 = a299;
			a312 = 34;
			a382 = (((((a382 * 5) - -11924) / 5) % 107) - -46);
			a201 = ((((a201 % 94) + 83) - -2021) + -2019);
			a224 = 36;
			a383 = a226[3];
			a276 = a289;
			a378 = 1;
			a395 = 0;
			a269 = 35;
			a260 = 0;
			a398 = 11;
			a240 = 0;
			a207 = 34;
			a146 = 1;
			a300 = 0;
			a392 = a304;
			a338 = 10;
			a359 = 6;
			a46 = a18;
			a358 = a348;
			a373 = 0;
			a228 = a292;
			a211 = 2;
			a225 = a205[0];
			a310 = ((((a310 - 145) * 1) - -5039) - 4966);
			a230 = 8;
			a313 = 35;
			a357 = ((((a357 + 12871) * 2) - 42771) + 25608);
			a256 = 36;
			a13 = (((19 - 15553) * 1) + 15620);
		}
	}
	if (((a81 == a167[2] && (a338 == 5 && (((-12 < a201) && (178 >= a201)) && (((input == inputs[9] && cf == 1) && a75 == 34) && a158 == 4)))) && ((a57 == 12 && (((-156 < a243) && (-68 >= a243)) && (a383 == a226[2] && a202 == a217[2]))) && a207 == 34))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a174 += (a174 + 20) > a174 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a35 -= (a35 - 20) < a35 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a75 = 32;
		a173 = 34;
		a172 = (a338 - -2);
		a99 = a26[((a172 / a158) - 1)];
	}
	if ((((a237 == 5 && (a158 == 4 && (((a81 == a167[2] && cf == 1) && a57 == 12) && a75 == 34))) && a313 == 34) && (((a338 == 5 && (((147 < a333) && (177 >= a333)) && a302 == a346[2])) && input == inputs[8]) && a269 == 34))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a98 -= (a98 - 20) < a98 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a31 += (a31 + 20) > a31 ? 4 : 0;
		cf = 0;
		a278 = a326[((a57 - a57) + 2)];
		a57 = (a320 + 8);
		a395 = 0;
		a40 = a65;
	}
	if (((a211 == 3 && (((-12 < a201) && (178 >= a201)) && (a359 == 5 && a57 == 12))) && (((a230 == 5 && (a302 == a346[2] && (((input == inputs[1] && cf == 1) && a158 == 4) && a81 == a167[2]))) && a75 == 34) && a338 == 5))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if (((a125 == a30[0] && !(a177 == 33)) && a383 == a226[3])) {
			a69 = 35;
			a143 = 36;
			a57 = ((a320 / a206) - -10);
		} else {
			a329 = 36;
			a310 = (((a310 + 10925) + 16347) / 5);
			a276 = a253;
			a370 = a318;
			a392 = a304;
			a338 = 10;
			a235 = a216[3];
			a361 = 33;
			a313 = 35;
			a382 = ((((a382 / 5) - -16611) * 10) / 9);
			a75 = 32;
			a307 = a227[4];
			a173 = 32;
			a230 = 10;
			a225 = a205[6];
			a129 = a92[(a398 - 11)];
			a270 = 16;
			a240 = 1;
			a302 = a346[6];
			a357 = (((((a357 * 5) % 38) + -17) - 15500) + 15499);
			a324 = a232[6];
			a201 = (((a201 * 5) - -21691) - -3046);
			a202 = a217[0];
			a125 = a30[(a211 + 4)];
		}
	}
	if (((((input == inputs[0] && ((((a57 == 12 && cf == 1) && a81 == a167[2]) && a75 == 34) && a361 == 34)) && a158 == 4) && a234 == a372[2]) && ((a336 == 1 && ((56 == a265[2]) && ((147 < a333) && (177 >= a333)))) && a338 == 5))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a162 -= (a162 - 20) < a162 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		a44 = 32;
		a75 = 33;
		a132 = 0;
		a77 = (a57 + -4);
	}
	if (((a324 == a232[2] && (((a75 == 34 && (a81 == a167[2] && cf == 1)) && input == inputs[5]) && a57 == 12)) && ((((a302 == a346[2] && ((47 == a239[4]) && a158 == 4)) && a336 == 1) && a211 == 3) && a224 == 34))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a35 -= (a35 - 20) < a35 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		if ((!(a81 == 4) && (a97 != 1 && (a221 != 1 || (a141 == 14 && !(27 == a46[0])))))) {
			a57 = (a158 - -10);
			a134 = 0;
			a71 = a175[(a57 - 13)];
		} else {
			a57 = (a398 + 5);
			a40 = a83;
			a25 = a68;
		}
	}
	if (((((a81 == a167[2] && ((a57 == 12 && ((147 < a333) && (177 >= a333))) && a158 == 4)) && (77 == a358[0])) && ((148 < a277) && (339 >= a277))) && (a269 == 34 && (((-12 < a201) && (178 >= a201)) && (a300 == 1 && ((cf == 1 && a75 == 34) && input == inputs[4])))))) {
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if ((a256 == 35 || a132 != 1)) {
			a57 = ((a320 + a230) + 2);
			a141 = a47[(a338 - -2)];
			a72 = ((((89 - 10928) * 2) * 10) / 9);
		} else {
			a361 = 35;
			a398 = 14;
			a173 = 34;
			a302 = a346[3];
			a230 = 3;
			a256 = 34;
			a339 = 1;
			a353 = a263;
			a333 = (((a333 - -2462) - -12820) * 1);
			a129 = a92[(a359 - 4)];
			a378 = 1;
			a235 = a216[3];
			a338 = 10;
			a392 = a304;
			a386 = (((((a386 % 61) - -262) * 5) % 61) - -245);
			a357 = (((a357 - -13824) * 2) + 139);
			a382 = (((a382 + 3719) / 5) * 5);
			a370 = a311;
			a206 = 8;
			a265 = a303;
			a211 = 5;
			a225 = a205[6];
			a313 = 35;
			a228 = a264;
			a310 = ((((a310 * 12) / 10) + 3095) * 5);
			a237 = 7;
			a243 = (((((a243 % 43) - 72) * 10) / 9) - 8);
			a312 = 35;
			a358 = a351;
			a270 = 13;
			a249 = ((((a249 * 5) + 14753) * 10) / 9);
			a296 = a212;
			a224 = 36;
			a300 = 1;
			a320 = 11;
			a240 = 1;
			a75 = 32;
			a207 = 35;
			a234 = a372[6];
			a307 = a227[6];
			a269 = 33;
			a202 = a217[1];
			a276 = a253;
			a172 = (a158 - 3);
			a336 = 1;
			a218 = 34;
			a201 = ((((a201 / 5) - 3) * 5) - -16);
			a329 = 35;
			a373 = 0;
			a368 = 1;
			a359 = 10;
		}
	}
}
void calculate_outputm129(int input) {
	if ((((38 == a370[4]) && (a313 == 34 && (((77 == a358[0]) && (((a57 == 12 && cf == 1) && a75 == 34) && a320 == 8)) && a211 == 3))) && (a158 == 5 && (a81 == a167[2] && (a300 == 1 && input == inputs[4]))))) {
		a174 += (a174 + 20) > a174 ? 4 : 0;
		cf = 0;
		a154 = ((a158 * a206) + -15);
		a249 = ((((((a249 * a277) % 14999) + 6368) - 26667) * 10) / 9);
		a392 = a257;
		a224 = 32;
		a57 = (a359 - -8);
		a230 = (a338 + -1);
		a310 = (((((((a310 * a386) % 14999) - 21422) % 77) + 258) + 19761) + -19706);
		a370 = a285;
		a137 = a189;
		a235 = a216[(a57 - 13)];
		a206 = (a320 - 4);
		a313 = 33;
		a361 = 33;
		a277 = ((((((a277 * a333) % 14999) / 5) % 78) + -7) / 5);
		a320 = ((a154 * a211) - 39);
	}
}
void calculate_outputm131(int input) {
	if (((a398 == 12 && (a302 == a346[2] && (a398 == 12 && (a75 == 34 && ((148 < a277) && (339 >= a277)))))) && (a158 == 9 && (input == inputs[6] && (a202 == a217[2] && ((a57 == 12 && (a81 == a167[2] && cf == 1)) && ((-57 < a357) && (20 >= a357)))))))) {
		cf = 0;
		if ((a125 == 5 && ((-10 < a13) && (203 >= a13)))) {
			a307 = a227[(a57 - 11)];
			a339 = 0;
			a75 = 32;
			a125 = a30[(a237 + 2)];
			a206 = (a57 - 7);
			a302 = a346[(a230 - 4)];
			a269 = 32;
			a218 = 32;
			a357 = (((((a357 * a201) - 3100) % 65) - 122) - 1);
			a310 = (((((((a310 * a277) % 14999) / 5) / 5) - -2120) % 77) - -161);
			a368 = 0;
			a359 = (a237 - 1);
			a211 = ((a270 + a237) + -14);
			a358 = a351;
			a239 = a299;
			a243 = ((((((a243 * a201) % 14999) - 26940) % 11) + -166) + -2);
			a173 = 32;
			a336 = 0;
			a398 = a270;
			a338 = (a57 - 8);
			a249 = (((((((a249 * a382) % 14999) % 101) + 254) - -1) - -23191) + -23192);
			a324 = a232[((a158 + a57) + -20)];
			a235 = a216[(a237 + -4)];
			a378 = 0;
			a333 = (((((((a333 * a201) % 14999) + -2497) % 96) + 122) - 23003) - -22971);
			a207 = 32;
			a320 = (a237 + 2);
			a230 = ((a206 - a398) + 10);
			a276 = a289;
			a240 = 0;
			a202 = a217[(a158 + -8)];
			a370 = a285;
			a224 = 33;
			a129 = a92[(a57 - 10)];
			a392 = a257;
			a237 = ((a320 * a320) - 45);
		} else {
			a173 = 36;
			a239 = a299;
			a211 = ((a230 + a230) - 8);
			a357 = (((((((a386 * a382) % 65) - 63) * 10) / 9) - 10964) - -10975);
			a310 = (((((((a201 * a277) % 14999) % 77) + 237) - -1) / 5) - -206);
			a338 = ((a230 + a230) - 6);
			a240 = 0;
			a202 = a217[(a230 + -4)];
			a218 = 32;
			a336 = 0;
			a237 = (a230 - 1);
			a307 = a227[(a230 - 4)];
			a224 = 32;
			a141 = a47[(a57 + -5)];
			a234 = a372[(a270 + -10)];
			a275 = a223;
			a235 = a216[((a158 / a338) + -1)];
			a324 = a232[(a230 + -4)];
			a249 = ((((((a249 * a357) % 14999) % 101) - -253) - -1) * 1);
			a243 = ((((((a243 * a201) % 14999) % 11) + -166) - 2) - -1);
			a302 = a346[(a230 - 4)];
			a333 = ((((((((a333 * a310) % 14999) % 96) - 5) - -51) * 5) % 96) + 19);
			a358 = a351;
			a392 = a257;
			a378 = 0;
			a370 = a285;
			a269 = 32;
			a359 = (a230 + -1);
			a75 = 32;
			a206 = (a398 - 7);
			a339 = 0;
			a353 = a241;
			a207 = 32;
			a320 = (a230 - -2);
			a368 = 0;
			a276 = a289;
			a398 = (a230 + 6);
			a230 = ((a359 + a359) + -4);
		}
	}
	if (((input == inputs[5] && (((a307 == a227[2] && a378 == 1) && a158 == 9) && a81 == a167[2])) && (a269 == 34 && ((a240 == 1 && (a218 == 34 && ((cf == 1 && a57 == 12) && a75 == 34))) && (77 == a358[0]))))) {
		cf = 0;
		a270 = ((a57 * a57) + -133);
		a206 = ((a338 / a237) + 4);
		a373 = 0;
		a370 = a285;
		a256 = 34;
		a171 = 36;
		a201 = ((((((a249 * a277) % 14999) / 5) + 15725) % 93) - 140);
		a296 = a384;
		a240 = 0;
		a230 = ((a338 - a237) + 5);
		a202 = a217[(a57 - 12)];
		a395 = 1;
		a312 = 32;
		a361 = 32;
		a235 = a216[((a211 + a57) - 12)];
		a295 = a366[((a158 * a158) + -79)];
		a383 = a226[((a57 / a57) + 1)];
		a260 = 0;
		a313 = 32;
		a277 = (((((((a277 * a249) % 14999) + -23040) - -33261) / 5) % 78) + -7);
		a269 = 33;
		a382 = ((((((a249 * a310) % 14999) % 12) - 54) + -25921) - -25916);
		a307 = a227[(a398 - 11)];
		a333 = ((((a333 * a357) - 6051) - -1656) - 2595);
		a224 = 33;
		a310 = ((((((a249 * a249) % 14999) / 5) + 6868) % 77) - -195);
		a353 = a263;
		a329 = 34;
		a358 = a348;
		a265 = a376;
		a225 = a205[(a57 + -11)];
		a237 = a359;
		a392 = a257;
		a75 = 35;
		a286 = a294[(a57 + -10)];
		a134 = 0;
		a398 = (a211 + 10);
		a368 = 0;
		a218 = 33;
		a386 = ((((70 * 15) / 10) - 27) * 1);
		a243 = ((((a243 * a357) - 18099) / 5) / 5);
		a300 = 1;
		a234 = a372[(a57 - 12)];
		a378 = 1;
		a249 = (((53 - 3397) / 5) - -924);
		a357 = ((((83 + -891) - -739) * 9) / 10);
		a302 = a346[((a206 / a320) + 1)];
	}
}
void calculate_outputm132(int input) {
	if (((((316 < a310) && (357 >= a310)) && (((a378 == 1 && a373 != 1) && a300 == 1) && a81 == a167[2])) && (((a158 == 11 && (a57 == 12 && (input == inputs[9] && (a75 == 34 && cf == 1)))) && a378 == 1) && a378 == 1))) {
		a120 -= (a120 - 20) < a120 ? 4 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		if ((!(50 == a228[0]) || (!(a256 == 34) || (((-57 < a357) && (20 >= a357)) && a307 == 2)))) {
			a146 = 0;
			a73 = (((93 * 5) / 5) + -23335);
			a75 = 36;
			a39 = a144;
		} else {
			a75 = 33;
			a132 = 0;
			a44 = 32;
			a77 = ((a270 - a158) + 7);
		}
	}
	if ((((((a75 == 34 && (input == inputs[7] && cf == 1)) && (47 == a239[4])) && a158 == 11) && a57 == 12) && (((a383 == a226[2] && (a359 == 5 && (a286 == a294[2] && a230 == 5))) && a81 == a167[2]) && (92 == a296[2])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a98 += (a98 + 20) > a98 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		a31 += (a31 + 20) > a31 ? 4 : 0;
		cf = 0;
		a324 = a232[4];
		a269 = 33;
		a386 = (((a386 - -28946) * 1) * -1);
		a125 = a30[((a158 + a57) + -22)];
		a336 = 0;
		a228 = a229;
		a312 = 32;
		a234 = a372[3];
		a202 = a217[0];
		a270 = 14;
		a260 = 1;
		a329 = 33;
		a307 = a227[5];
		a300 = 0;
		a207 = 35;
		a224 = 36;
		a286 = a294[7];
		a75 = 32;
		a398 = 10;
		a378 = 0;
		a338 = 3;
		a235 = a216[5];
		a237 = 7;
		a359 = 8;
		a243 = (((a243 * -5) + -21395) - -32781);
		a249 = ((((a249 - -5603) + -18777) * 2) + 50337);
		a256 = 35;
		a296 = a362;
		a240 = 1;
		a370 = a311;
		a310 = ((((a310 + -4465) + -4432) % 20) + 337);
		a302 = a346[6];
		a382 = ((((a382 % 107) - -69) + 11469) + -11469);
		a201 = (((a201 + 27721) + -3107) / 5);
		a320 = 7;
		a395 = 1;
		a361 = 32;
		a206 = 8;
		a373 = 0;
		a265 = a293;
		a230 = 8;
		a357 = ((((((a357 % 38) + -18) * 5) * 5) % 38) + -17);
		a339 = 1;
		a383 = a226[3];
		a218 = 36;
		a368 = 0;
		a353 = a399;
		a239 = a268;
		a276 = a250;
		a333 = (((a333 + 3436) - -26326) + 24);
		a392 = a304;
		a173 = 32;
		a211 = 5;
		a277 = (((((a277 / 5) * 5) * 5) * -1) / 10);
		a8 = a158;
	}
	if (((a286 == a294[2] && (a57 == 12 && a302 == a346[2])) && (((-12 < a201) && (178 >= a201)) && (((38 == a370[4]) && ((50 == a392[4]) && (input == inputs[1] && (a158 == 11 && (a75 == 34 && (a81 == a167[2] && cf == 1)))))) && ((-57 < a357) && (20 >= a357)))))) {
		a164 += (a164 + 20) > a164 ? 2 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a158 = (a230 - -4);
		a3 = a114;
		a57 = (a158 - -1);
	}
	if (((input == inputs[3] && (a234 == a372[2] && a75 == 34)) && (a230 == 5 && (a256 == 34 && (a286 == a294[2] && ((((a81 == a167[2] && (a57 == 12 && cf == 1)) && ((355 < a249) && (499 >= a249))) && a158 == 11) && a368 == 1)))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;

	}
	if ((((a307 == a227[2] && (((47 == a239[4]) && input == inputs[4]) && a206 == 6)) && a398 == 12) && (((a158 == 11 && (a312 == 34 && ((cf == 1 && a75 == 34) && a81 == a167[2]))) && a57 == 12) && (110 == a276[2])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if (((9 == a274[0]) || ((241 < a54) && (402 >= a54)))) {
			a173 = 36;
			a42 = ((a158 * a57) + -125);
			a75 = 32;
			a141 = a47[(a158 - 10)];
		} else {
			a278 = a326[(a158 - 9)];
			a57 = (a158 + 5);
			a40 = a65;
		}
	}
	if (((((50 == a392[4]) && (((cf == 1 && a75 == 34) && a57 == 12) && a81 == a167[2])) && (110 == a276[2])) && (a324 == a232[2] && (a329 == 34 && (((((-156 < a243) && (-68 >= a243)) && input == inputs[0]) && (92 == a296[2])) && a158 == 11))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if ((((cf == 1 || a286 == 6) || a329 == 34) && a368 != 1)) {
			a256 = 35;
			a395 = 1;
			a276 = a253;
			a239 = a299;
			a336 = 1;
			a260 = 0;
			a370 = a311;
			a353 = a241;
			a240 = 1;
			a383 = a226[5];
			a392 = a304;
			a202 = a217[3];
			a398 = 12;
			a125 = a30[(a270 - 8)];
			a338 = 10;
			a224 = 33;
			a75 = 32;
			a234 = a372[0];
			a357 = ((((a357 / 5) + -4) + -21642) + 21609);
			a307 = a227[4];
			a218 = 35;
			a359 = 6;
			a237 = 8;
			a358 = a351;
			a277 = (((a277 + 9710) / 5) * 5);
			a207 = 33;
			a312 = 33;
			a339 = 1;
			a201 = (((a201 * 5) + -7971) * 3);
			a206 = 9;
			a378 = 1;
			a243 = ((((a243 * 10) / 3) + -24615) * 1);
			a302 = a346[0];
			a368 = 1;
			a382 = (((a382 / 5) + 28207) + 1321);
			a230 = 3;
			a324 = a232[7];
			a211 = 5;
			a310 = ((((((a310 % 20) + 329) * 5) + 14711) % 20) - -320);
			a373 = 1;
			a249 = ((((a249 / 5) * 5) - 19966) + 19808);
			a296 = a384;
			a286 = a294[6];
			a333 = (((a333 + 10630) - -9913) / 5);
			a210 = 0;
			a173 = 32;
			a269 = 34;
			a225 = a205[0];
			a265 = a376;
			a235 = a216[0];
			a329 = 33;
			a300 = 1;
			a228 = a264;
			a320 = 6;
			a270 = 13;
		} else {
			a278 = a326[((a57 - a57) + 2)];
			a57 = ((a320 + a211) + 5);
			a40 = a65;
		}
	}
	if ((((((a329 == 34 && (a158 == 11 && a218 == 34)) && a75 == 34) && a329 == 34) && (15 == a353[2])) && (a359 == 5 && ((a81 == a167[2] && ((a57 == 12 && cf == 1) && input == inputs[2])) && a234 == a372[2])))) {
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a132 = 1;
		a75 = 33;
		a123 = 1;
		a137 = a117;
	}
	if (((a81 == a167[2] && (input == inputs[6] && (((50 == a392[4]) && ((201 < a386) && (325 >= a386))) && a218 == 34))) && ((59 == a228[3]) && (a373 != 1 && (a75 == 34 && ((a57 == 12 && (cf == 1 && a158 == 11)) && a339 != 1)))))) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if (((!(a237 == 7) && ((((164 < a54) && (241 >= a54)) || ((276 < a130) && (493 >= a130))) || a329 == 35)) && a14 == 11)) {
			a302 = a346[7];
			a218 = 33;
			a276 = a253;
			a310 = ((((a310 - -24852) - 34967) / 5) - -2290);
			a392 = a304;
			a270 = 14;
			a173 = 32;
			a324 = a232[2];
			a75 = 32;
			a286 = a294[6];
			a329 = 35;
			a382 = ((((a382 - -17139) * 10) / 9) - -566);
			a240 = 1;
			a357 = (((a357 - 7581) * 3) * 1);
			a201 = (((a201 - 12641) - -4752) + -16323);
			a228 = a229;
			a81 = a167[((a359 - a57) + 7)];
			a370 = a318;
			a249 = (((a249 * 5) * 5) - -3065);
			a230 = 9;
			a125 = a30[((a158 - a57) - -6)];
		} else {
			a286 = a294[4];
			a313 = 33;
			a225 = a205[6];
			a358 = a351;
			a368 = 0;
			a361 = 33;
			a339 = 0;
			a395 = 1;
			a158 = (a359 - 1);
		}
	}
	if (((a202 == a217[2] && (((-39 < a382) && (176 >= a382)) && (a224 == 34 && a286 == a294[2]))) && (a75 == 34 && (a57 == 12 && (((((input == inputs[8] && cf == 1) && a158 == 11) && a256 == 34) && a81 == a167[2]) && a300 == 1))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a324 = a232[3];
		a57 = (a230 - -5);
		a392 = a208;
		a333 = (((a333 + 746) + 9989) * 2);
		a270 = 11;
		a276 = a250;
		a158 = ((a211 * a237) + -9);
		a269 = 35;
		a378 = 0;
		a260 = 0;
		a225 = a205[6];
		a277 = ((((a277 % 95) + 156) + 34) + -1);
		a228 = a264;
		a358 = a348;
		a312 = 34;
		a239 = a299;
		a386 = (((((a386 * 5) % 61) + 229) + -13417) + 13408);
		a373 = 0;
		a202 = a217[3];
		a235 = a216[1];
		a243 = ((((((a243 % 11) - 164) + 4) / 5) * 49) / 10);
		a230 = 4;
		a361 = 35;
		a370 = a318;
		a398 = 12;
		a313 = 36;
		a105 = 34;
		a201 = (((a201 - -24445) * 1) * 1);
		a211 = 5;
	}
	if ((((a395 == 1 && (a75 == 34 && ((a81 == a167[2] && cf == 1) && a57 == 12))) && (92 == a296[2])) && ((input == inputs[5] && ((((147 < a333) && (177 >= a333)) && ((15 == a353[2]) && ((355 < a249) && (499 >= a249)))) && a158 == 11)) && a286 == a294[2]))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a75 = 36;
		a46 = a148;
		a146 = 1;
		a72 = ((((((2 * 5) * 259) / 10) / 5) * 51) / 10);
	}
}
void calculate_outputm135(int input) {
	if ((((38 == a370[4]) && (a57 == 12 && (a336 == 1 && a81 == a167[5]))) && (((-12 < a201) && (178 >= a201)) && ((a170 <= 26 && (((-39 < a382) && (176 >= a382)) && (a218 == 34 && ((input == inputs[1] && cf == 1) && a75 == 34)))) && a368 == 1)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a158 = ((a57 / a57) + 6);
		a13 = ((((((a170 * a170) % 14999) * 2) % 14995) - 15004) - 2);
		a57 = (a158 + 3);
	}
	if ((((a170 <= 26 && (a81 == a167[5] && ((110 == a276[2]) && (input == inputs[6] && (a57 == 12 && cf == 1))))) && a378 == 1) && (a373 != 1 && (a211 == 3 && ((a218 == 34 && a75 == 34) && ((-156 < a243) && (-68 >= a243))))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a174 += (a174 + 20) > a174 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a158 = ((a211 - a338) - -7);
		a200 = a115[((a270 - a158) - 1)];
		a57 = (a359 + 5);
	}
	if ((((a320 == 8 && ((a81 == a167[5] && (77 == a358[0])) && a57 == 12)) && (15 == a353[2])) && (a211 == 3 && (((a75 == 34 && ((a170 <= 26 && cf == 1) && input == inputs[3])) && a307 == a227[2]) && a307 == a227[2])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 += (a164 + 20) > a164 ? 3 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a134 = 1;
		a57 = 16;
		a278 = a326[(a57 + -10)];
	}
	if (((a260 == 1 && ((a57 == 12 && (((a170 <= 26 && ((input == inputs[8] && cf == 1) && a81 == a167[5])) && ((-156 < a243) && (-68 >= a243))) && a307 == a227[2])) && (47 == a239[4]))) && (a75 == 34 && (a336 == 1 && (92 == a296[2]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a94 -= (a94 - 20) < a94 ? 2 : 0;
		cf = 0;
		a125 = a30[(a206 - 1)];
		a173 = 32;
		a75 = 32;
		a81 = a167[(a270 - 9)];
	}
	if (((a225 == a205[2] && ((a300 == 1 && (((a81 == a167[5] && (a75 == 34 && cf == 1)) && a398 == 12) && a57 == 12)) && a170 <= 26)) && (a235 == a216[2] && ((input == inputs[2] && ((-39 < a382) && (176 >= a382))) && a368 == 1)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a75 = 32;
		a173 = 35;
		a91 = (a57 - 1);
		a1 = a87[(a91 - 7)];
	}
	if (((a240 == 1 && ((a307 == a227[2] && (a75 == 34 && a329 == 34)) && (110 == a276[2]))) && ((((a57 == 12 && (a81 == a167[5] && (input == inputs[5] && cf == 1))) && ((201 < a386) && (325 >= a386))) && a170 <= 26) && ((-39 < a382) && (176 >= a382))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		a31 += (a31 + 20) > a31 ? 1 : 0;
		cf = 0;
		a143 = 36;
		a69 = 32;
		a57 = (a398 - 1);
	}
	if (((((a240 == 1 && (((-12 < a201) && (178 >= a201)) && ((cf == 1 && a57 == 12) && a81 == a167[5]))) && (92 == a296[2])) && a75 == 34) && ((((a170 <= 26 && a286 == a294[2]) && input == inputs[9]) && a302 == a346[2]) && ((-39 < a382) && (176 >= a382))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a67 += (a67 + 20) > a67 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if ((!(a244 == 12) || (a240 == 1 || ((!(a129 == 10) || a235 == 11) || !(a81 == 5))))) {
			a201 = ((((a201 + 15164) * 10) / 9) + 46);
			a357 = (((((a357 - 24057) % 38) - 15) * 9) / 10);
			a392 = a208;
			a324 = a232[4];
			a207 = 33;
			a382 = (((a382 - 14975) * 1) - 11238);
			a313 = 33;
			a333 = ((((88 * -6) / 10) + -27058) * 1);
			a249 = (((((a249 * 10) / 15) + -19) - -14044) - 14084);
			a300 = 0;
			a398 = 12;
			a235 = a216[7];
			a312 = 35;
			a265 = a293;
			a336 = 0;
			a202 = a217[0];
			a206 = 8;
			a230 = 9;
			a383 = a226[0];
			a218 = 36;
			a173 = 32;
			a239 = a268;
			a276 = a250;
			a240 = 1;
			a224 = 34;
			a234 = a372[7];
			a225 = a205[7];
			a339 = 1;
			a378 = 0;
			a361 = 36;
			a8 = (a237 - -6);
			a125 = a30[(a270 + -11)];
			a256 = 36;
			a237 = 3;
			a277 = (((((a277 + 11301) % 95) + 237) / 5) - -171);
			a260 = 1;
			a370 = a311;
			a243 = ((((a243 * 5) + 18318) % 43) + -152);
			a302 = a346[0];
			a386 = ((((a386 - 910) % 61) + 321) + 1);
			a395 = 1;
			a296 = a362;
			a211 = 7;
			a307 = a227[0];
			a359 = 3;
			a368 = 0;
			a329 = 33;
			a75 = 32;
			a269 = 32;
			a320 = 9;
			a353 = a399;
			a286 = a294[2];
			a338 = 6;
			a358 = a335;
			a373 = 0;
			a270 = 13;
		} else {
			a69 = 34;
			a143 = 36;
			a57 = (a206 + 5);
		}
	}
	if ((((((((56 == a265[2]) && a361 == 34) && a324 == a232[2]) && a378 == 1) && input == inputs[0]) && a57 == 12) && (a75 == 34 && ((((a81 == a167[5] && cf == 1) && a170 <= 26) && a339 != 1) && ((148 < a277) && (339 >= a277)))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a40 = a83;
		a57 = (a338 - -12);
		a25 = a68;
	}
	if ((((47 == a239[4]) && (a324 == a232[2] && a312 == 34)) && ((a338 == 5 && ((15 == a353[2]) && (a57 == 12 && (((355 < a249) && (499 >= a249)) && (a170 <= 26 && ((cf == 1 && a81 == a167[5]) && a75 == 34)))))) && input == inputs[7]))) {
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a132 = 0;
		a75 = 33;
		a129 = a92[(a320 - 3)];
		a77 = a57;
	}
	if (((a81 == a167[5] && (a359 == 5 && (((355 < a249) && (499 >= a249)) && (a339 != 1 && (a57 == 12 && (((cf == 1 && a170 <= 26) && a75 == 34) && input == inputs[4])))))) && ((a398 == 12 && a338 == 5) && a313 == 34))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a51 += (a51 + 20) > a51 ? 3 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		a179 = (((((((a386 * a386) % 14999) % 40) - 27) + -23713) / 5) - -4701);
		a81 = a167[((a57 + a320) - 16)];
	}
}
void calculate_outputm137(int input) {
	if ((((a207 == 34 && (((a224 == 34 && (a57 == 12 && (cf == 1 && a75 == 34))) && input == inputs[4]) && a81 == a167[7])) && a323 == 9) && ((((15 == a353[2]) && a218 == 34) && ((147 < a333) && (177 >= a333))) && (38 == a370[4])))) {
		a178 += (a178 + 20) > a178 ? 4 : 0;
		cf = 0;
		if ((((a278 == a326[5] && cf == 1) && !(a202 == a217[5])) || !(a14 == a79[6]))) {
			a277 = (((((((a277 * a333) % 14999) + -23601) * 1) / 5) % 78) - -81);
			a137 = a189;
			a57 = (a230 + 8);
			a154 = ((a57 - a211) - -5);
			a207 = 32;
			a361 = 33;
			a230 = (a57 + -9);
			a249 = (((((a249 * a357) + 18944) % 15076) - 14923) + 0);
			a206 = (a154 + -11);
			a370 = a285;
			a224 = 32;
			a235 = a216[(a154 - 15)];
			a310 = ((((((((a310 * a386) % 14999) % 77) + 176) * 10) / 9) * 10) / 9);
			a225 = a205[(a154 + -15)];
		} else {
			a57 = (a359 - -6);
			a329 = 32;
			a296 = a212;
			a312 = 33;
			a207 = 32;
			a270 = (a57 - -1);
			a265 = a376;
			a225 = a205[(a211 + -3)];
			a173 = 33;
			a249 = (((((a249 * a277) % 14999) + -1147) / 5) + -7398);
			a398 = (a57 + 1);
			a338 = (a323 - 6);
			a277 = ((((((a243 * a333) % 78) - -103) + -25) * 9) / 10);
			a224 = 32;
			a201 = ((((((a382 * a243) % 94) + 84) - 2) - -5301) - 5299);
			a320 = (a270 + -4);
			a228 = a229;
			a206 = (a270 - 8);
			a370 = a285;
			a276 = a253;
			a339 = 1;
			a234 = a372[((a57 * a323) - 97)];
			a211 = (a230 + -4);
			a143 = 34;
			a260 = 1;
			a373 = 0;
			a368 = 1;
			a235 = a216[((a323 * a320) + -72)];
			a359 = (a398 - 9);
			a310 = ((((((a310 * a243) % 14999) % 77) - -239) + -28219) + 28219);
		}
	}
}
void calculate_outputm10(int input) {
	if ((((((50 == a392[4]) && ((((316 < a310) && (357 >= a310)) && a224 == 34) && a235 == a216[2])) && a206 == 6) && (15 == a353[2])) && (cf == 1 && a81 == a167[2]))) {
		if ((((a361 == 34 && (a230 == 5 && (a158 == 4 && cf == 1))) && a235 == a216[2]) && (a202 == a217[2] && (a312 == 34 && a218 == 34)))) {
			calculate_outputm128(input);
		}
		if (((a211 == 3 && (((cf == 1 && a158 == 5) && a324 == a232[2]) && a361 == 34)) && (((110 == a276[2]) && a383 == a226[2]) && a338 == 5))) {
			calculate_outputm129(input);
		}
		if ((((77 == a358[0]) && ((38 == a370[4]) && (((147 < a333) && (177 >= a333)) && (cf == 1 && a158 == 9)))) && ((a368 == 1 && a378 == 1) && a237 == 5))) {
			calculate_outputm131(input);
		}
		if (((((a211 == 3 && a211 == 3) && a368 == 1) && (59 == a228[3])) && ((110 == a276[2]) && ((cf == 1 && a158 == 11) && (56 == a265[2]))))) {
			calculate_outputm132(input);
		}
	}
	if (((a359 == 5 && ((a206 == 6 && a286 == a294[2]) && a237 == 5)) && (a338 == 5 && ((cf == 1 && a81 == a167[5]) && a240 == 1)))) {
		if (((((a211 == 3 && a207 == 34) && a202 == a217[2]) && a378 == 1) && ((50 == a392[4]) && (a302 == a346[2] && (a170 <= 26 && cf == 1))))) {
			calculate_outputm135(input);
		}
	}
	if (((a235 == a216[2] && (((59 == a228[3]) && a302 == a346[2]) && ((316 < a310) && (357 >= a310)))) && ((a329 == 34 && (a81 == a167[7] && cf == 1)) && a225 == a205[2]))) {
		if ((((cf == 1 && a323 == 9) && a218 == 34) && (((a336 == 1 && (a361 == 34 && a324 == a232[2])) && a206 == 6) && ((355 < a249) && (499 >= a249))))) {
			calculate_outputm137(input);
		}
	}
}
void calculate_outputm138(int input) {
	if (((a75 == 34 && (((cf == 1 && (20 == a137[1])) && input == inputs[5]) && a154 == 10)) && (((((a57 == 13 && (a224 == 34 && (56 == a265[2]))) && (56 == a265[2])) && a336 == 1) && a234 == a372[2]) && ((-39 < a382) && (176 >= a382))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		cf = 0;
		a134 = 0;
		a75 = 35;
		a295 = a366[((a57 + a154) - 18)];
		a53 = (((((a386 * a243) % 14999) - -27153) - -472) - -381);
	}
	if (((a235 == a216[2] && (((20 == a137[1]) && a202 == a217[2]) && a256 == 34)) && (a237 == 5 && (((((a154 == 10 && (cf == 1 && a57 == 13)) && a211 == 3) && input == inputs[7]) && a307 == a227[2]) && a75 == 34)))) {
		a164 += (a164 + 20) > a164 ? 4 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a75 = 33;
		a132 = 0;
		a155 = 32;
		a77 = (a154 + -3);
	}
	if ((((a211 == 3 && (a206 == 6 && (a256 == 34 && a57 == 13))) && a286 == a294[2]) && ((a154 == 10 && ((((cf == 1 && a75 == 34) && input == inputs[6]) && a225 == a205[2]) && (20 == a137[1]))) && a207 == 34))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a169 -= (a169 - 20) < a169 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if ((((147 < a333) && (177 >= a333)) || a260 == 1)) {
			a370 = a318;
			a329 = 35;
			a240 = 1;
			a202 = a217[7];
			a276 = a253;
			a172 = ((a57 / a230) - -5);
			a206 = 4;
			a75 = 32;
			a382 = (((a382 + 2568) - -13881) * 1);
			a353 = a399;
			a218 = 33;
			a207 = 35;
			a269 = 32;
			a225 = a205[7];
			a235 = a216[7];
			a357 = (((a357 + -14792) + -76) + -12963);
			a256 = 33;
			a237 = 9;
			a398 = 10;
			a358 = a348;
			a270 = 13;
			a234 = a372[4];
			a338 = 7;
			a395 = 1;
			a211 = 8;
			a310 = (((a310 + -13607) + 29461) / 5);
			a224 = 36;
			a386 = ((((((a386 % 61) + 252) - 49) / 5) * 55) / 10);
			a336 = 1;
			a359 = 9;
			a296 = a384;
			a239 = a242;
			a230 = 8;
			a339 = 1;
			a173 = 34;
			a249 = ((((59 - 29662) / 5) * 5) + 29920);
			a302 = a346[0];
			a333 = ((((((a333 % 14) - -156) + 1) / 5) * 48) / 10);
			a373 = 1;
			a286 = a294[3];
			a300 = 1;
			a320 = 12;
			a228 = a229;
			a260 = 1;
			a361 = 35;
			a243 = ((((a243 - 2775) + 5473) + -7681) * -5);
			a201 = (((((a201 % 94) + 83) + -1) + 19883) - 19881);
			a368 = 1;
			a324 = a232[0];
			a312 = 34;
			a307 = a227[1];
			a277 = (((((a277 * 10) / 4) / 5) + -27063) - -37928);
			a265 = a303;
			a99 = a26[((a57 - a172) + -1)];
		} else {
			a358 = a348;
			a324 = a232[7];
			a211 = 8;
			a357 = (((((a357 % 38) + -18) * 5) % 38) + -18);
			a395 = 1;
			a230 = 8;
			a300 = 1;
			a201 = (((((a201 % 94) + 83) + -19156) + 11678) - -7479);
			a361 = 35;
			a312 = 35;
			a234 = a372[4];
			a370 = a318;
			a338 = 3;
			a302 = a346[6];
			a269 = 36;
			a339 = 1;
			a336 = 1;
			a333 = (((a333 * 5) * 5) + -29731);
			a320 = 6;
			a75 = 32;
			a359 = 5;
			a286 = a294[0];
			a277 = ((((((a277 % 95) + 164) * 10) / 9) - -28310) + -28262);
			a225 = a205[0];
			a224 = 36;
			a368 = 1;
			a123 = 0;
			a276 = a253;
			a218 = 35;
			a260 = 1;
			a235 = a216[7];
			a373 = 1;
			a256 = 36;
			a307 = a227[7];
			a173 = 36;
			a206 = 9;
			a207 = 36;
			a270 = 17;
			a329 = 33;
			a240 = 1;
			a310 = (((a310 - -22744) - -428) + -17332);
			a237 = 9;
			a382 = (((a382 - 8905) - 18713) - 1992);
			a265 = a376;
			a353 = a263;
			a141 = a47[(a57 - 13)];
		}
	}
	if ((((56 == a265[2]) && ((a230 == 5 && ((((47 == a239[4]) && (20 == a137[1])) && input == inputs[1]) && ((316 < a310) && (357 >= a310)))) && (77 == a358[0]))) && (a395 == 1 && (a57 == 13 && (a154 == 10 && (a75 == 34 && cf == 1)))))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a162 += (a162 + 20) > a162 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		if (((258 < a72 && a295 == a366[3]) && a225 == a205[4])) {
			a320 = 11;
			a336 = 0;
			a91 = (a154 + 3);
			a277 = (((((((a277 % 95) + 154) * 10) / 9) * 5) % 95) - -192);
			a398 = 17;
			a324 = a232[5];
			a395 = 0;
			a312 = 34;
			a249 = ((((90 - -23590) * 10) / 9) * 1);
			a207 = 35;
			a370 = a311;
			a230 = 10;
			a361 = 32;
			a368 = 0;
			a270 = 11;
			a234 = a372[3];
			a373 = 0;
			a211 = 7;
			a206 = 7;
			a353 = a241;
			a237 = 8;
			a235 = a216[7];
			a386 = ((((a386 / 5) + 164) + 11837) - 11758);
			a228 = a264;
			a329 = 32;
			a392 = a304;
			a196 = (a359 - -12);
			a269 = 34;
			a225 = a205[4];
			a378 = 0;
			a286 = a294[3];
			a224 = 36;
			a338 = 5;
			a307 = a227[5];
			a256 = 34;
			a239 = a268;
			a75 = 35;
			a265 = a293;
			a300 = 0;
			a383 = a226[6];
			a339 = 0;
			a382 = ((((a382 - -20967) * 1) % 107) - 11);
			a240 = 0;
			a134 = 1;
			a296 = a384;
			a358 = a351;
			a243 = (((a243 / 5) - 444) + 298);
			a260 = 0;
			a276 = a289;
			a333 = ((((a333 - 25031) + 24900) * 9) / 10);
			a201 = ((((a201 + 3716) % 94) - 8) - 3);
			a310 = ((((a310 % 20) + 326) * 5) / 5);
			a359 = 7;
		} else {
			a230 = 7;
			a276 = a253;
			a395 = 1;
			a386 = (((a386 - 25429) * 1) / 5);
			a75 = 32;
			a358 = a335;
			a225 = a205[3];
			a338 = 7;
			a310 = (((a310 + 18437) - 18507) - 23880);
			a357 = (((a357 + 27275) - -1928) - -235);
			a218 = 35;
			a398 = 17;
			a173 = 32;
			a300 = 1;
			a336 = 1;
			a382 = (((a382 - -29804) - 44817) + 39530);
			a256 = 33;
			a237 = 9;
			a206 = 11;
			a228 = a229;
			a286 = a294[6];
			a240 = 1;
			a302 = a346[2];
			a339 = 0;
			a239 = a242;
			a368 = 1;
			a235 = a216[5];
			a201 = (((a201 - 26842) - 2086) + -554);
			a333 = ((((a333 + -4287) - 6746) * 10) / 9);
			a202 = a217[4];
			a312 = 32;
			a361 = 34;
			a243 = ((((a243 % 43) + -70) - -1) - -1);
			a320 = 12;
			a324 = a232[2];
			a307 = a227[4];
			a329 = 34;
			a370 = a311;
			a359 = 7;
			a373 = 1;
			a207 = 35;
			a81 = a167[(a270 - 10)];
			a125 = a30[(a154 + -5)];
			a277 = ((((a277 - -17228) - 10489) * 10) / 9);
			a211 = 8;
			a296 = a362;
			a260 = 1;
			a270 = 15;
		}
	}
	if ((((a240 == 1 && ((((cf == 1 && a75 == 34) && a57 == 13) && a302 == a346[2]) && a154 == 10)) && a338 == 5) && ((20 == a137[1]) && ((a398 == 12 && ((47 == a239[4]) && a207 == 34)) && input == inputs[0])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if (a75 == 32) {
			a57 = (a320 + 8);
			a249 = ((((((75 + -20420) * -1) / 10) / 5) * 13) / 10);
			a228 = a264;
			a370 = a311;
			a383 = a226[6];
			a382 = (((((a382 + -22880) % 107) - -139) - 13770) + 13777);
			a276 = a253;
			a313 = 36;
			a269 = 34;
			a378 = 0;
			a392 = a208;
			a339 = 0;
			a312 = 32;
			a358 = a335;
			a81 = a167[(a270 + -12)];
			a278 = a326[(a57 - 9)];
		} else {
			a129 = a92[(a57 - 13)];
			a75 = 35;
			a134 = 1;
			a196 = ((a206 * a154) + -50);
		}
	}
	if (((a154 == 10 && (((a57 == 13 && (cf == 1 && a75 == 34)) && (77 == a358[0])) && a361 == 34)) && ((20 == a137[1]) && (input == inputs[9] && (a286 == a294[2] && ((a234 == a372[2] && a240 == 1) && a234 == a372[2])))))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 4 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a172 = (a230 + -4);
		a173 = 34;
		a75 = 32;
		a129 = a92[(a172 - -2)];
	}
	if (((((-12 < a201) && (178 >= a201)) && ((cf == 1 && a57 == 13) && a154 == 10)) && (a235 == a216[2] && (a359 == 5 && (input == inputs[8] && ((a75 == 34 && ((15 == a353[2]) && (((-57 < a357) && (20 >= a357)) && (20 == a137[1])))) && a336 == 1)))))) {
		a169 -= (a169 - 20) < a169 ? 4 : 0;
		a98 += (a98 + 20) > a98 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if (a99 == 6) {
			a134 = 1;
			a129 = a92[(a359 + 2)];
			a75 = 35;
			a196 = (a211 - -7);
		} else {
			a40 = a65;
			a141 = a47[(a57 - 7)];
			a57 = ((a270 + a270) + -7);
		}
	}
	if (((a256 == 34 && (((cf == 1 && input == inputs[4]) && a75 == 34) && (77 == a358[0]))) && (((((((77 == a358[0]) && a211 == 3) && (59 == a228[3])) && (20 == a137[1])) && a154 == 10) && a57 == 13) && a235 == a216[2]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a174 += (a174 + 20) > a174 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a276 = a253;
		a324 = a232[7];
		a277 = ((((a277 / 5) + 162) + 21921) + -21856);
		a173 = 33;
		a225 = a205[5];
		a357 = (((a357 - 16994) - 12672) + -276);
		a75 = 32;
		a239 = a268;
		a310 = (((a310 * 5) + 9364) * 2);
		a224 = 36;
		a269 = 36;
		a243 = (((((((a243 % 43) - 90) * 9) / 10) * 5) % 43) + -106);
		a206 = 7;
		a359 = 7;
		a235 = a216[2];
		a270 = 17;
		a339 = 1;
		a191 = a37[((a237 + a211) + -3)];
		a240 = 1;
		a130 = (((93 / 5) + -17133) * 1);
	}
	if ((((((20 == a137[1]) && ((a57 == 13 && (((-156 < a243) && (-68 >= a243)) && input == inputs[3])) && a230 == 5)) && ((201 < a386) && (325 >= a386))) && a336 == 1) && (a307 == a227[2] && (a373 != 1 && (a75 == 34 && (a154 == 10 && cf == 1)))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a169 -= (a169 - 20) < a169 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a224 = 32;
		a228 = a264;
		a296 = a362;
		a218 = 36;
		a320 = 9;
		a336 = 0;
		a339 = 0;
		a359 = 4;
		a361 = 36;
		a75 = 35;
		a398 = 13;
		a295 = a366[((a57 + a57) + -21)];
		a276 = a250;
		a269 = 32;
		a134 = 0;
		a333 = ((((a333 / 5) - -5456) * 10) / 9);
		a234 = a372[4];
		a373 = 0;
		a202 = a217[4];
		a239 = a268;
		a392 = a257;
		a358 = a351;
		a211 = 4;
		a53 = (((((((a386 * a310) % 14999) % 59) + -15) * 5) % 59) + 14);
	}
	if (((input == inputs[2] && ((((a154 == 10 && (cf == 1 && (20 == a137[1]))) && a260 == 1) && a230 == 5) && a269 == 34)) && ((a75 == 34 && ((((-39 < a382) && (176 >= a382)) && (38 == a370[4])) && a225 == a205[2])) && a57 == 13))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a164 -= (a164 - 20) < a164 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		if (a373 == 1) {
			a296 = a212;
			a230 = 5;
			a329 = 36;
			a336 = 1;
			a398 = 10;
			a313 = 36;
			a361 = 33;
			a368 = 1;
			a269 = 34;
			a158 = ((a211 * a359) + -4);
			a202 = a217[2];
			a201 = (((a201 + 8332) + 6842) * 1);
			a276 = a250;
			a155 = 36;
			a249 = (((((8 + 362) * 10) / 9) * 9) / 10);
			a333 = (((a333 - 4547) - 9147) - 10224);
			a277 = (((((a277 * 23) / 10) / 5) * 10) / 2);
			a235 = a216[0];
			a378 = 1;
			a310 = ((((a310 + 19898) * -1) * 10) / 9);
			a339 = 1;
			a312 = 33;
			a224 = 35;
			a286 = a294[6];
			a234 = a372[1];
			a392 = a208;
			a324 = a232[5];
			a206 = 6;
			a383 = a226[6];
			a237 = 7;
			a57 = (a211 - -7);
		} else {
			a235 = a216[2];
			a240 = 1;
			a237 = 5;
			a276 = a253;
			a172 = ((a57 * a154) + -129);
			a307 = a227[0];
			a211 = 4;
			a386 = (((a386 + -24132) + -6035) + -29);
			a270 = 12;
			a230 = 9;
			a359 = 10;
			a296 = a212;
			a357 = ((((a357 - 24434) % 38) - -20) - 37);
			a75 = 32;
			a243 = (((a243 + -18629) + -10440) - 643);
			a260 = 1;
			a333 = ((((((a333 % 14) + 161) * 5) - -16297) % 14) + 150);
			a324 = a232[4];
			a265 = a303;
			a338 = 10;
			a382 = ((((a382 * 5) % 107) + 68) + 0);
			a225 = a205[4];
			a336 = 1;
			a218 = 34;
			a300 = 1;
			a207 = 35;
			a370 = a318;
			a368 = 1;
			a202 = a217[2];
			a269 = 33;
			a373 = 1;
			a361 = 35;
			a286 = a294[7];
			a320 = 12;
			a398 = 17;
			a310 = (((a310 - 6817) - 8156) + -6750);
			a329 = 33;
			a256 = 35;
			a312 = 34;
			a239 = a268;
			a383 = a226[1];
			a358 = a335;
			a302 = a346[6];
			a206 = 9;
			a201 = (((a201 + -8632) - 11284) - 2860);
			a395 = 1;
			a228 = a264;
			a224 = 36;
			a173 = 34;
			a339 = 1;
			a129 = a92[(a172 + a172)];
		}
	}
}
void calculate_outputm139(int input) {
	if (((((a269 == 34 && ((147 < a333) && (177 >= a333))) && a202 == a217[2]) && a154 == 11) && (((a256 == 34 && (((a57 == 13 && (input == inputs[3] && cf == 1)) && (20 == a137[1])) && a75 == 34)) && a300 == 1) && (110 == a276[2])))) {
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		cf = 0;
		a339 = 0;
		a353 = a241;
		a357 = (((((((a357 * a277) % 65) - 121) / 5) * 5) % 65) + -80);
		a75 = 32;
		a240 = 0;
		a392 = a257;
		a329 = 32;
		a42 = ((a398 - a57) + 2);
		a141 = a47[((a237 * a211) - 14)];
		a237 = (a359 - 1);
		a260 = 0;
		a269 = 32;
		a173 = 36;
		a310 = (((((((a310 * a357) % 14999) + -13738) + 34656) * 1) % 77) - -177);
	}
	if (((((148 < a277) && (339 >= a277)) && (a75 == 34 && ((a398 == 12 && (a256 == 34 && (a154 == 11 && ((20 == a137[1]) && cf == 1)))) && input == inputs[5]))) && (a57 == 13 && (a307 == a227[2] && (a260 == 1 && (15 == a353[2])))))) {
		a67 += (a67 + 20) > a67 ? 1 : 0;
		cf = 0;
		a370 = a285;
		a270 = (a338 + 5);
		a158 = (a398 - 6);
		a206 = ((a237 + a211) - 2);
		a373 = 1;
		a395 = 1;
		a361 = 33;
		a392 = a257;
		a57 = (a359 - -5);
		a312 = 33;
		a378 = 1;
		a324 = a232[(a154 + -11)];
		a260 = 1;
		a313 = 34;
		a228 = a229;
		a201 = (((((((a310 * a310) % 14999) / 5) % 93) + -145) / 5) + -158);
		a243 = ((((((a333 * a277) % 14999) - 27289) + -101) - -17015) + -13158);
		a269 = 32;
		a207 = 34;
		a386 = (((((a277 * a333) % 14999) - 16413) / 5) * 5);
		a277 = ((((a277 * a357) + -1583) * 1) - 7962);
		a235 = a216[(a211 - 3)];
		a276 = a253;
		a239 = a242;
		a211 = ((a398 + a398) + -22);
		a398 = a57;
		a105 = 34;
		a202 = a217[(a320 + -8)];
		a333 = ((((((a333 * a382) % 14999) + 13800) % 14976) - 15022) * 1);
	}
}
void calculate_outputm140(int input) {
	if (((a378 == 1 && ((a234 == a372[2] && (input == inputs[8] && (cf == 1 && a154 == 12))) && a75 == 34)) && ((((((-39 < a382) && (176 >= a382)) && (((-156 < a243) && (-68 >= a243)) && a202 == a217[2])) && (20 == a137[1])) && ((-12 < a201) && (178 >= a201))) && a57 == 13))) {
		a51 += (a51 + 20) > a51 ? 3 : 0;
		cf = 0;
		a339 = 1;
		a329 = 32;
		a207 = 32;
		a276 = a253;
		a312 = 33;
		a228 = a229;
		a143 = 34;
		a277 = (((((((a277 * a382) % 14999) / 5) + 4813) + 6948) % 78) - -20);
		a368 = 1;
		a173 = 33;
		a57 = (a338 - -6);
		a395 = 0;
		a359 = (a338 - 2);
		a313 = 33;
		a338 = (a398 - 9);
	}
	if (((a75 == 34 && ((a57 == 13 && ((201 < a386) && (325 >= a386))) && a207 == 34)) && ((a398 == 12 && (((input == inputs[4] && ((cf == 1 && a154 == 12) && (20 == a137[1]))) && ((147 < a333) && (177 >= a333))) && a329 == 34)) && a286 == a294[2]))) {
		a164 += (a164 + 20) > a164 ? 1 : 0;
		cf = 0;
		a368 = 1;
		a207 = 32;
		a276 = a253;
		a312 = 33;
		a228 = a229;
		a313 = 33;
		a143 = 34;
		a338 = (a398 + -9);
		a173 = 33;
		a329 = 32;
		a339 = 1;
		a359 = (a398 + -9);
		a57 = ((a154 * a154) + -133);
		a395 = 0;
		a277 = (((((a277 * a357) % 78) + 69) + 2) + -2);
	}
}
void calculate_outputm141(int input) {
	if ((((a324 == a232[2] && (a211 == 3 && (a57 == 13 && ((cf == 1 && a154 == 15) && input == inputs[6])))) && a300 == 1) && (a75 == 34 && ((20 == a137[1]) && ((a269 == 34 && a218 == 34) && (59 == a228[3])))))) {
		a164 -= (a164 - 20) < a164 ? 4 : 0;
		cf = 0;
		a382 = (((((((a382 * a249) % 14999) / 5) - 21925) - -30412) * -1) / 10);
		a240 = 1;
		a135 = 34;
		a307 = a227[(a206 - 3)];
		a312 = 33;
		a353 = a241;
		a296 = a212;
		a211 = (a206 + -3);
		a228 = a229;
		a196 = (a57 - -2);
		a134 = 1;
		a329 = 32;
		a218 = 33;
		a276 = a253;
		a333 = ((((((a333 * a357) - 15311) + 19877) * 3) % 14976) + -15022);
		a339 = 1;
		a338 = ((a154 / a237) - 2);
		a359 = (a320 - 3);
		a368 = 1;
		a324 = a232[(a320 / a320)];
		a75 = 35;
		a357 = ((((((a357 * a249) % 14999) + 11006) * 1) % 65) + -122);
	}
}
void calculate_outputm142(int input) {
	if ((((((77 == a358[0]) && ((56 == a265[2]) && ((201 < a386) && (325 >= a386)))) && a339 != 1) && (input == inputs[6] && (a75 == 34 && ((20 == a137[1]) && (((56 == a265[2]) && (a57 == 13 && (a154 == 16 && cf == 1))) && ((-39 < a382) && (176 >= a382))))))) && (a110 % 2 == 0))) {
		cf = 0;
		a143 = 32;
		a14 = a79[((a57 * a270) - 152)];
		a57 = (a237 + 6);
	}
	if (((((a75 == 34 && (a206 == 6 && ((((a329 == 34 && ((a57 == 13 && cf == 1) && (20 == a137[1]))) && input == inputs[3]) && a361 == 34) && (56 == a265[2])))) && a207 == 34) && ((15 == a353[2]) && a154 == 16)) && a90 == 9680)) {
		a168 += (a168 + 20) > a168 ? 4 : 0;
		cf = 0;
		a132 = 0;
		a75 = 33;
		a155 = 34;
		a77 = ((a359 * a359) + -18);
	}
	if ((((a302 == a346[2] && (((a218 == 34 && a307 == a227[2]) && a75 == 34) && a339 != 1)) && a361 == 34) && ((a57 == 13 && (a154 == 16 && (input == inputs[9] && (cf == 1 && (20 == a137[1]))))) && a313 == 34))) {
		a178 -= (a178 - 20) < a178 ? 4 : 0;
		a181 += (a181 + 20) > a181 ? 4 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		cf = 0;
		a296 = a384;
		a353 = a241;
		a368 = 0;
		a218 = 32;
		a265 = a293;
		a339 = 0;
		a224 = 32;
		a338 = 4;
		a230 = a338;
		a276 = a289;
		a386 = ((((((a310 * a357) % 61) + 138) / 5) + 28757) + -28687);
		a302 = a346[((a270 + a57) + -24)];
		a206 = ((a237 + a230) + -4);
		a129 = a92[(a154 + -15)];
		a370 = a285;
		a361 = 32;
		a172 = ((a320 - a398) - -5);
		a358 = a348;
		a373 = 1;
		a398 = (a57 - 2);
		a228 = a229;
		a307 = a227[(a398 - 10)];
		a286 = a294[(a211 + -2)];
		a270 = (a338 - -7);
		a395 = 0;
		a382 = (((((((a386 * a243) % 14999) % 12) + -52) - -2) + 5594) + -5596);
		a320 = ((a57 * a57) + -162);
		a173 = 34;
		a234 = a372[(a338 - 4)];
		a207 = 32;
		a312 = 32;
		a237 = ((a230 * a338) + -12);
		a240 = 0;
		a333 = (((((a333 * a357) % 96) + 49) - 0) - -1);
		a329 = 32;
		a249 = ((((((a249 * a357) * 1) % 101) + 254) / 5) - -245);
		a392 = a257;
		a211 = (a338 / a338);
		a75 = 32;
		a359 = (a398 + -7);
		a260 = 0;
		a336 = 0;
		a202 = a217[(a338 - 4)];
		a313 = 32;
		a225 = a205[((a230 + a338) + -7)];
		a357 = (((((a357 * a382) / 5) % 65) + -121) * 1);
	}
	if ((((((50 == a392[4]) && ((20 == a137[1]) && (input == inputs[8] && (a202 == a217[2] && a202 == a217[2])))) && a206 == 6) && ((59 == a228[3]) && ((((355 < a249) && (499 >= a249)) && ((cf == 1 && a57 == 13) && a154 == 16)) && a75 == 34))) && a178 <= 3)) {
		a178 += (a178 + 20) > a178 ? 1 : 0;
		cf = 0;
		a392 = a257;
		a270 = (a359 - -6);
		a324 = a232[((a320 * a270) - 87)];
		a370 = a285;
		a276 = a289;
		a382 = ((((((a382 * a310) % 14999) / 5) + -21218) % 12) - 49);
		a228 = a264;
		a81 = a167[(a57 - 13)];
		a125 = a30[((a211 - a320) - -10)];
		a230 = ((a398 * a398) - 140);
		a173 = 32;
		a286 = a294[(a211 + -2)];
		a75 = 32;
		a357 = (((((a357 * a386) % 65) + -122) - -12303) - 12302);
		a240 = 0;
		a329 = 32;
		a218 = 32;
		a313 = 32;
		a249 = ((((((((a249 * a310) % 14999) % 101) - -209) * 9) / 10) * 10) / 9);
		a260 = 0;
		a302 = a346[((a206 + a338) - 10)];
	}
	if ((((a329 == 34 && ((92 == a296[2]) && (((20 == a137[1]) && a336 == 1) && input == inputs[1]))) && (a218 == 34 && ((a57 == 13 && (a234 == a372[2] && ((cf == 1 && a154 == 16) && a75 == 34))) && a320 == 8))) && a5 >= 7)) {
		cf = 0;
		a265 = a293;
		a218 = 32;
		a368 = 0;
		a338 = (a237 - 1);
		a329 = 32;
		a207 = 32;
		a172 = ((a320 - a57) + 9);
		a313 = 32;
		a240 = 0;
		a224 = 32;
		a302 = a346[(a206 - 5)];
		a270 = ((a206 + a211) + 2);
		a75 = 32;
		a370 = a285;
		a173 = 34;
		a357 = ((((((a357 * a382) % 65) - 121) * 1) + -28874) + 28872);
		a392 = a257;
		a274 = a245;
		a373 = 0;
		a320 = ((a206 - a359) + 6);
	}
	if (((a206 == 6 && ((input == inputs[2] && (a75 == 34 && (a154 == 16 && cf == 1))) && (38 == a370[4]))) && ((((92 == a296[2]) && ((a57 == 13 && a398 == 12) && (20 == a137[1]))) && (77 == a358[0])) && a359 == 5))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		cf = 0;
		a358 = a348;
		a378 = 1;
		a269 = 33;
		a201 = (((((((a357 * a382) % 94) + 82) * 5) - -27427) % 94) + -7);
		a228 = a229;
		a310 = (((((a201 * a357) - -6581) + 15570) % 20) - -318);
		a235 = a216[((a211 - a230) - -4)];
		a278 = a326[((a320 / a237) - -6)];
		a300 = 1;
		a382 = ((((((a382 * a333) % 14999) * 2) + 3) % 12) + -52);
		a276 = a289;
		a339 = 1;
		a57 = (a230 - -11);
		a81 = a167[(a230 + -5)];
		a312 = 33;
		a256 = 34;
		a370 = a285;
		a243 = ((((((((a333 * a249) % 14999) % 43) - 150) * 9) / 10) - 28985) + 28997);
	}
	if (((((92 == a296[2]) && ((20 == a137[1]) && (((a57 == 13 && a373 != 1) && ((147 < a333) && (177 >= a333))) && a395 == 1))) && (((a361 == 34 && ((cf == 1 && input == inputs[4]) && a154 == 16)) && a75 == 34) && (92 == a296[2]))) && a98 == 9886)) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		cf = 0;
		a177 = 34;
		a75 = 33;
		a132 = 1;
		a137 = a116;
	}
	if (((((15 == a353[2]) && ((38 == a370[4]) && ((a313 == 34 && (38 == a370[4])) && (20 == a137[1])))) && a224 == 34) && (a230 == 5 && ((a75 == 34 && ((input == inputs[0] && cf == 1) && a154 == 16)) && a57 == 13)))) {
		a50 += (a50 + 20) > a50 ? 4 : 0;
		cf = 0;
		a249 = ((((((a249 * a382) % 14999) * 2) % 15076) - 14923) * 1);
		a143 = 34;
		a329 = 32;
		a256 = 33;
		a201 = (((((((a333 * a333) % 14999) % 94) - -30) / 5) * 10) / 9);
		a235 = a216[(a359 - 5)];
		a228 = a229;
		a173 = 33;
		a237 = a211;
		a277 = ((((((a386 * a201) % 14999) % 78) - -69) / 5) * 5);
		a395 = 0;
		a57 = (a154 - 5);
		a207 = 32;
		a300 = 1;
		a312 = 33;
		a296 = a212;
		a225 = a205[(a320 - a320)];
		a368 = 1;
		a276 = a253;
		a339 = 1;
		a224 = 32;
		a392 = a257;
		a206 = (a359 + -1);
		a313 = 33;
		a359 = (a154 + -13);
		a378 = 1;
		a338 = ((a154 * a211) + -45);
		a370 = a285;
		a211 = ((a398 - a270) + 1);
	}
	if ((((((a57 == 13 && (a320 == 8 && (((a154 == 16 && cf == 1) && (20 == a137[1])) && a75 == 34))) && a225 == a205[2]) && a373 != 1) && (a312 == 34 && ((input == inputs[7] && ((147 < a333) && (177 >= a333))) && a313 == 34))) && a162 >= 2)) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		cf = 0;
		a69 = 35;
		a143 = 36;
		a57 = (a398 + -1);
		a201 = (((((a357 * a382) % 94) + 83) / 5) / 5);
	}
	if ((((a202 == a217[2] && (a260 == 1 && ((20 == a137[1]) && ((a57 == 13 && (a75 == 34 && (input == inputs[5] && cf == 1))) && a154 == 16)))) && ((((355 < a249) && (499 >= a249)) && (a338 == 5 && (38 == a370[4]))) && ((355 < a249) && (499 >= a249)))) && (a56 % 2 == 0))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		cf = 0;
		a155 = 32;
		a132 = 0;
		a75 = 33;
		a77 = (a154 - 9);
	}
}
void calculate_outputm143(int input) {
	if (((((a359 == 5 && a307 == a227[2]) && (47 == a239[4])) && input == inputs[1]) && (a286 == a294[2] && (a295 == a366[2] && (a336 == 1 && ((((cf == 1 && (26 == a137[1])) && a75 == 34) && a57 == 13) && a218 == 34)))))) {
		a120 -= (a120 - 20) < a120 ? 4 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		if (405 < a19) {
			a310 = ((((a310 + 8948) % 20) + 332) + -11);
			a173 = 33;
			a357 = (((a357 + -12113) * 2) * 1);
			a191 = a37[(a398 + -7)];
			a324 = a232[6];
			a243 = (((((a243 % 43) + -104) - 1) + -15305) + 15308);
			a75 = 32;
			a339 = 1;
			a240 = 1;
			a206 = 10;
			a378 = 1;
			a270 = 10;
			a224 = 35;
			a313 = 33;
			a239 = a268;
			a359 = 8;
			a269 = 35;
			a130 = (((38 + -8630) - -38166) / -5);
		} else {
			a173 = 32;
			a81 = a167[(a338 + -2)];
			a75 = 32;
			a125 = a30[(a270 + -7)];
		}
	}
	if (((((a300 == 1 && (((201 < a386) && (325 >= a386)) && (((26 == a137[1]) && (cf == 1 && input == inputs[4])) && a295 == a366[2]))) && a368 == 1) && a339 != 1) && (((316 < a310) && (357 >= a310)) && (a57 == 13 && (a75 == 34 && a383 == a226[2]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a174 += (a174 + 20) > a174 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a1 = a87[(a270 - 6)];
		a260 = 1;
		a300 = 1;
		a302 = a346[6];
		a249 = (((a249 / -5) - 3450) * 5);
		a75 = 32;
		a224 = 33;
		a235 = a216[4];
		a310 = (((a310 / -5) - 14560) / 5);
		a269 = 36;
		a243 = ((((a243 - 10702) * 10) / 9) * 2);
		a361 = 34;
		a211 = 7;
		a173 = 35;
		a202 = a217[5];
		a234 = a372[2];
		a324 = a232[3];
		a240 = 1;
		a336 = 1;
		a206 = 7;
		a286 = a294[3];
		a239 = a268;
		a333 = ((((a333 / 5) - -125) / 5) + 136);
		a312 = 33;
		a359 = 8;
		a358 = a335;
		a265 = a303;
		a307 = a227[2];
		a320 = 13;
		a368 = 1;
		a237 = 8;
		a225 = a205[6];
		a91 = (a398 + -1);
		a230 = 6;
		a218 = 34;
		a270 = 17;
		a228 = a292;
		a313 = 36;
		a383 = a226[7];
		a353 = a399;
		a378 = 1;
		a386 = (((a386 - 20092) / 5) * 5);
		a357 = ((((a357 - 15304) * 10) / -9) + 9275);
		a339 = 1;
		a382 = ((((a382 * 5) % 107) - -68) / 5);
		a373 = 1;
		a398 = 16;
	}
	if ((((a240 == 1 && ((((201 < a386) && (325 >= a386)) && a295 == a366[2]) && a57 == 13)) && a234 == a372[2]) && (a312 == 34 && (a256 == 34 && (a336 == 1 && (((26 == a137[1]) && (cf == 1 && input == inputs[2])) && a75 == 34)))))) {
		a164 += (a164 + 20) > a164 ? 2 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		a230 = 7;
		a16 = 1;
		a382 = ((((a382 - 18318) + -5243) * 10) / 9);
		a313 = 35;
		a353 = a399;
		a359 = 5;
		a336 = 0;
		a276 = a289;
		a378 = 0;
		a333 = (((a333 + 5447) * 5) * 1);
		a270 = 13;
		a338 = 7;
		a368 = 0;
		a392 = a257;
		a225 = a205[4];
		a310 = (((a310 - -11509) + -11651) + -9);
		a358 = a335;
		a277 = ((((38 - -11590) + -27841) / 5) + 3307);
		a218 = 34;
		a300 = 1;
		a296 = a384;
		a286 = a294[1];
		a386 = (((((a386 % 61) + 215) - -16) * 10) / 9);
		a234 = a372[3];
		a249 = ((((a249 * 15) / 10) - -16471) - -4334);
		a207 = 32;
		a206 = 7;
		a201 = ((((52 + -27630) + 27693) * 10) / 9);
		a320 = 11;
		a357 = (((((a357 % 38) - 18) + -24637) / 5) + 4920);
		a307 = a227[4];
		a260 = 0;
		a383 = a226[1];
		a339 = 0;
		a228 = a292;
		a312 = 32;
		a324 = a232[7];
		a132 = 0;
		a75 = 33;
		a256 = 34;
		a361 = 34;
		a235 = a216[5];
		a398 = 14;
		a395 = 0;
		a211 = 7;
		a265 = a303;
		a329 = 36;
		a269 = 34;
		a239 = a268;
		a370 = a285;
		a224 = 35;
		a202 = a217[5];
		a237 = 7;
		a243 = ((((a243 * 5) * 5) % 43) + -93);
		a77 = (a57 - 4);
	}
	if (((((201 < a386) && (325 >= a386)) && (a202 == a217[2] && (input == inputs[5] && (((a75 == 34 && cf == 1) && a57 == 13) && a207 == 34)))) && ((a218 == 34 && ((26 == a137[1]) && (a302 == a346[2] && a324 == a232[2]))) && a295 == a366[2]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a169 -= (a169 - 20) < a169 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a329 = 34;
		a357 = (((a357 + -3937) - 2081) - 22055);
		a368 = 0;
		a324 = a232[2];
		a398 = 14;
		a338 = 9;
		a234 = a372[6];
		a313 = 35;
		a382 = ((((a382 / 5) - 731) * 5) + 3652);
		a196 = (a270 - -3);
		a310 = (((a310 + 20340) - -1410) - -4939);
		a361 = 35;
		a135 = 34;
		a211 = 7;
		a224 = 33;
		a218 = 34;
		a333 = ((((a333 + 11400) - 34175) + -3816) - -36148);
		a249 = ((((a249 - 16383) % 71) - -462) + 14);
		a312 = 32;
		a225 = a205[3];
		a296 = a384;
		a206 = 5;
		a256 = 32;
		a240 = 0;
		a307 = a227[4];
		a134 = 1;
		a320 = 7;
		a353 = a263;
		a207 = 36;
		a339 = 0;
		a276 = a250;
		a260 = 1;
		a359 = 10;
		a235 = a216[6];
		a230 = 9;
		a75 = 35;
		a228 = a292;
		a237 = 5;
		a270 = 17;
	}
	if (((a269 == 34 && (a398 == 12 && ((((a57 == 13 && ((26 == a137[1]) && cf == 1)) && a361 == 34) && a75 == 34) && ((-156 < a243) && (-68 >= a243))))) && (a313 == 34 && (input == inputs[8] && (a378 == 1 && a295 == a366[2]))))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a1 = a87[(a237 - 1)];
		a75 = 32;
		a173 = 35;
		a91 = ((a320 / a320) - -10);
	}
	if (((((a75 == 34 && a207 == 34) && a57 == 13) && (26 == a137[1])) && ((47 == a239[4]) && ((a234 == a372[2] && (a224 == 34 && ((a295 == a366[2] && (input == inputs[3] && cf == 1)) && a230 == 5))) && ((355 < a249) && (499 >= a249)))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a270 = 17;
		a265 = a376;
		a320 = 10;
		a239 = a299;
		a383 = a226[6];
		a286 = a294[7];
		a260 = 0;
		a256 = 34;
		a249 = ((((a249 % 71) - -369) - 7123) + 7148);
		a211 = 6;
		a300 = 1;
		a75 = 33;
		a382 = (((a382 + 12549) * 2) + 3495);
		a202 = a217[7];
		a277 = (((9 - 28565) + -986) * 1);
		a16 = 1;
		a225 = a205[4];
		a370 = a311;
		a368 = 0;
		a234 = a372[3];
		a230 = 4;
		a201 = (((18 + 29844) - -3) / 5);
		a361 = 32;
		a324 = a232[6];
		a296 = a384;
		a276 = a250;
		a312 = 35;
		a207 = 35;
		a398 = 14;
		a386 = ((((a386 * 10) / 17) + 18179) - 18171);
		a336 = 0;
		a338 = 6;
		a333 = (((a333 - -21453) / 5) / 5);
		a77 = (a206 + 3);
		a224 = 32;
		a132 = 0;
		a269 = 34;
		a243 = (((((a243 * 5) / 5) + 20494) % 43) - 136);
		a218 = 36;
		a228 = a264;
		a339 = 0;
		a395 = 0;
		a237 = 10;
		a358 = a335;
		a353 = a241;
		a392 = a304;
		a359 = 9;
		a310 = (((((a310 * 12) / 10) / 5) - 10873) + 14176);
		a378 = 0;
		a357 = ((((a357 / 5) / 5) + 10753) + -10736);
		a313 = 35;
		a235 = a216[7];
		a307 = a227[1];
		a329 = 34;
		a206 = 5;
	}
	if ((((((-39 < a382) && (176 >= a382)) && ((59 == a228[3]) && (((-156 < a243) && (-68 >= a243)) && (a383 == a226[2] && (a75 == 34 && (92 == a296[2])))))) && (26 == a137[1])) && (input == inputs[9] && (a218 == 34 && ((a57 == 13 && cf == 1) && a295 == a366[2]))))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a67 -= (a67 - 20) < a67 ? 4 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		cf = 0;
		if ((!(a200 == a115[0]) || a244 == a363[7])) {
			a81 = a167[(a206 + -6)];
			a99 = a26[(a270 + -10)];
			a57 = a270;
		} else {
			a141 = a47[(a320 + -1)];
			a72 = ((((1 * 5) - -21586) * 10) / -9);
			a57 = (a211 - -12);
		}
	}
	if ((((((47 == a239[4]) && (a269 == 34 && a218 == 34)) && a75 == 34) && a206 == 6) && ((59 == a228[3]) && (a339 != 1 && (((26 == a137[1]) && ((a295 == a366[2] && cf == 1) && a57 == 13)) && input == inputs[6]))))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a373 = 1;
		a277 = ((((92 * 37) / 10) + 27118) / 5);
		a235 = a216[3];
		a269 = 33;
		a265 = a293;
		a370 = a285;
		a276 = a253;
		a243 = ((((a243 % 43) - 78) / 5) + -94);
		a154 = ((a57 + a320) + -5);
		a225 = a205[4];
		a256 = 33;
		a383 = a226[5];
		a378 = 1;
		a310 = (((a310 / 5) + 15083) - 14806);
		a395 = 0;
		a300 = 1;
		a392 = a257;
		a137 = a189;
	}
	if ((((a359 == 5 && ((((355 < a249) && (499 >= a249)) && (((-39 < a382) && (176 >= a382)) && ((15 == a353[2]) && (a57 == 13 && ((26 == a137[1]) && a361 == 34))))) && a75 == 34)) && a240 == 1) && (a295 == a366[2] && (cf == 1 && input == inputs[7])))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if ((((a221 == 1 && a368 == 1) || a240 == 1) && a270 == 17)) {
			a373 = 1;
			a361 = 33;
			a57 = (a206 + 6);
			a260 = 1;
			a81 = a167[(a57 - 10)];
			a201 = ((((46 * 10) / -2) * 5) * 5);
			a392 = a257;
			a276 = a253;
			a313 = 35;
			a265 = a303;
			a358 = a348;
			a370 = a285;
			a235 = a216[6];
			a277 = (((70 / 5) - -15016) + 3057);
			a395 = 0;
			a158 = ((a237 / a237) - -10);
		} else {
			a392 = a257;
			a277 = ((((35 * -3) / 10) - 15215) - 1964);
			a235 = a216[6];
			a300 = 1;
			a378 = 1;
			a373 = 1;
			a395 = 0;
			a269 = 35;
			a154 = ((a230 + a359) + 6);
			a256 = 34;
			a370 = a318;
			a310 = (((a310 - -1875) / 5) - -13717);
			a225 = a205[3];
			a243 = (((a243 - -28752) + 825) * 1);
			a383 = a226[7];
			a276 = a253;
			a265 = a303;
			a137 = a189;
		}
	}
	if ((((a286 == a294[2] && (((-39 < a382) && (176 >= a382)) && (a75 == 34 && (a57 == 13 && ((26 == a137[1]) && (input == inputs[0] && cf == 1)))))) && a329 == 34) && (((a295 == a366[2] && ((355 < a249) && (499 >= a249))) && ((147 < a333) && (177 >= a333))) && a260 == 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a234 = a372[6];
		a359 = 4;
		a249 = (((((a249 + 16397) % 71) - -408) + -14166) + 14151);
		a339 = 0;
		a260 = 0;
		a392 = a257;
		a228 = a264;
		a368 = 0;
		a276 = a289;
		a54 = ((((((((a333 * a386) % 14999) % 80) - -319) * 9) / 10) / 5) - -225);
		a307 = a227[7];
		a357 = (((a357 + 23784) + -2651) * 1);
		a333 = ((((((a333 % 14) + 163) - 10) * 5) % 14) + 150);
		a230 = 4;
		a296 = a362;
		a201 = ((((76 - -27) * 5) + -3546) - -3042);
		a207 = 35;
		a75 = 35;
		a382 = ((((a382 - 26071) * 1) % 12) + -46);
		a202 = a217[5];
		a277 = ((((((92 * 10) / 2) * 10) / 9) * 10) / 9);
		a320 = 11;
		a240 = 0;
		a224 = 35;
		a237 = 4;
		a310 = ((((a310 + -11347) * 10) / -9) * 2);
		a361 = 36;
		a398 = 11;
		a239 = a299;
		a324 = a232[3];
		a270 = 15;
		a225 = a205[7];
		a370 = a311;
		a218 = 35;
		a206 = 6;
		a353 = a241;
		a329 = 34;
		a134 = 1;
		a378 = 0;
		a256 = 35;
		a300 = 0;
		a383 = a226[7];
		a211 = 7;
		a395 = 0;
		a358 = a335;
		a196 = (a57 - 1);
		a336 = 0;
		a338 = 8;
		a243 = ((((a243 + -17354) % 11) + -164) * 1);
		a235 = a216[6];
		a302 = a346[1];
		a312 = 34;
		a286 = a294[6];
		a313 = 34;
		a269 = 36;
		a386 = (((((a386 * 10) / 17) - 1064) + -8526) + 9596);
	}
}
void calculate_outputm144(int input) {
	if (((((a324 == a232[2] && a339 != 1) && (56 == a265[2])) && a307 == a227[2]) && ((((((a57 == 13 && (cf == 1 && (26 == a137[1]))) && input == inputs[3]) && a295 == a366[4]) && a75 == 34) && a359 == 5) && a368 == 1))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a67 -= (a67 - 20) < a67 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 2 : 0;
		a35 += (a35 + 20) > a35 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a383 = a226[7];
		a235 = a216[0];
		a382 = ((((a382 + 10002) + -36187) * 10) / -9);
		a276 = a253;
		a370 = a311;
		a302 = a346[0];
		a300 = 1;
		a312 = 34;
		a211 = 5;
		a320 = 10;
		a265 = a303;
		a338 = 3;
		a368 = 1;
		a310 = ((((a310 * 5) * 5) % 20) - -323);
		a392 = a304;
		a313 = 36;
		a373 = 1;
		a286 = a294[2];
		a75 = 32;
		a239 = a268;
		a225 = a205[7];
		a386 = (((a386 + -26562) + -684) - 2878);
		a142 = 0;
		a230 = 3;
		a307 = a227[4];
		a173 = 35;
		a243 = ((((a243 * 27) / 10) * 5) * 5);
		a336 = 1;
		a201 = ((((35 - 22531) * 1) * 10) / 9);
		a249 = (((((a249 % 71) + 390) / 5) / 5) - -478);
		a333 = (((a333 * 5) - -26986) * 1);
		a324 = a232[6];
		a256 = 34;
		a353 = a263;
		a269 = 33;
		a91 = ((a206 * a270) - 60);
		a218 = 33;
		a202 = a217[3];
		a234 = a372[7];
		a398 = 14;
		a339 = 1;
		a228 = a264;
		a206 = 11;
		a358 = a335;
		a240 = 1;
		a359 = 6;
		a260 = 1;
		a207 = 34;
		a329 = 35;
		a357 = (((a357 + 23598) - -5516) + 204);
		a395 = 1;
		a277 = (((a277 - 27781) - 1577) + -298);
		a237 = 5;
		a270 = 15;
	}
	if (((((355 < a249) && (499 >= a249)) && ((((316 < a310) && (357 >= a310)) && (50 == a392[4])) && a339 != 1)) && (a57 == 13 && (a234 == a372[2] && ((((a75 == 34 && ((26 == a137[1]) && cf == 1)) && a361 == 34) && a295 == a366[4]) && input == inputs[4]))))) {
		a120 -= (a120 - 20) < a120 ? 4 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a57 = (a211 + 12);
		a141 = a47[((a237 * a359) - 25)];
		a72 = (((((a386 * a386) % 14999) / 5) - -2963) + -6919);
	}
	if (((a329 == 34 && (a295 == a366[4] && (input == inputs[5] && a207 == 34))) && (a206 == 6 && (a338 == 5 && (((148 < a277) && (339 >= a277)) && ((a57 == 13 && (a75 == 34 && (cf == 1 && (26 == a137[1])))) && ((316 < a310) && (357 >= a310)))))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a361 = 36;
		a228 = a292;
		a172 = ((a57 / a57) - -6);
		a373 = 1;
		a260 = 1;
		a370 = a311;
		a353 = a399;
		a207 = 34;
		a240 = 1;
		a300 = 1;
		a256 = 35;
		a313 = 33;
		a249 = ((((a249 - -26957) - -1980) * 1) + -54618);
		a237 = 9;
		a211 = 6;
		a395 = 1;
		a234 = a372[7];
		a243 = ((((((a243 * 5) % 43) + -105) * 5) % 43) + -74);
		a357 = (((a357 - -23885) * 1) / 5);
		a99 = a26[(a230 + -4)];
		a173 = 34;
		a333 = ((((a333 % 14) - -162) + 14215) - 14213);
		a265 = a303;
		a276 = a250;
		a368 = 1;
		a358 = a351;
		a75 = 32;
		a307 = a227[7];
		a312 = 33;
		a320 = 11;
		a206 = 11;
		a382 = (((a382 + 24069) * 1) / 5);
		a336 = 1;
		a386 = (((a386 / 5) + 24358) - -6);
		a270 = 15;
		a398 = 17;
		a302 = a346[5];
		a235 = a216[3];
		a225 = a205[7];
		a339 = 1;
		a338 = 7;
		a392 = a304;
		a329 = 35;
		a359 = 10;
		a269 = 33;
		a218 = 36;
		a286 = a294[5];
		a310 = ((((a310 % 20) + 328) - -1) + 1);
		a230 = 5;
	}
	if ((((77 == a358[0]) && (a300 == 1 && (a373 != 1 && (a313 == 34 && a57 == 13)))) && ((15 == a353[2]) && (a75 == 34 && (((26 == a137[1]) && (input == inputs[0] && (cf == 1 && a295 == a366[4]))) && a286 == a294[2]))))) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a75 = 32;
		a125 = a30[((a398 * a230) + -59)];
		a173 = 32;
		a8 = (a57 - 1);
	}
	if ((((a225 == a205[2] && (a395 == 1 && ((a57 == 13 && (a295 == a366[4] && ((15 == a353[2]) && a398 == 12))) && (47 == a239[4])))) && a260 == 1) && (input == inputs[9] && (a75 == 34 && ((26 == a137[1]) && cf == 1))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a5 -= (a5 - 20) < a5 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a361 = 35;
		a237 = 7;
		a310 = ((((a310 - 24049) - 506) + -4101) + 51976);
		a230 = 10;
		a202 = a217[3];
		a378 = 0;
		a386 = (((((a386 - 25769) % 61) - -188) - 19576) - -19526);
		a234 = a372[7];
		a196 = (a57 + 4);
		a235 = a216[4];
		a256 = 32;
		a395 = 0;
		a224 = 35;
		a307 = a227[4];
		a392 = a257;
		a269 = 35;
		a276 = a289;
		a277 = ((((a277 - 21149) + -7734) % 95) + 296);
		a353 = a399;
		a339 = 0;
		a320 = 13;
		a270 = 12;
		a206 = 5;
		a296 = a384;
		a207 = 34;
		a324 = a232[7];
		a383 = a226[5];
		a333 = (((a333 * 5) + -770) / 5);
		a382 = ((((a382 % 12) - 50) / 5) - 39);
		a368 = 0;
		a338 = 7;
		a265 = a293;
		a373 = 0;
		a313 = 33;
		a239 = a268;
		a336 = 0;
		a370 = a285;
		a243 = ((((a243 % 43) + -82) + 12) + -21);
		a358 = a351;
		a228 = a292;
		a398 = 14;
		a329 = 34;
		a359 = 10;
		a134 = 1;
		a300 = 0;
		a286 = a294[4];
		a211 = 2;
		a240 = 0;
		a75 = 35;
		a225 = a205[4];
		a260 = 0;
		a91 = a57;
	}
	if (((((input == inputs[6] && (a338 == 5 && (a295 == a366[4] && (a57 == 13 && ((355 < a249) && (499 >= a249)))))) && a359 == 5) && a207 == 34) && (((a75 == 34 && ((26 == a137[1]) && cf == 1)) && (59 == a228[3])) && a234 == a372[2]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if ((!(a129 == a92[3]) || a59 == 32)) {
			a310 = (((((a310 + -2219) * 5) * 3) % 20) - -344);
			a211 = 2;
			a368 = 0;
			a357 = ((((a357 % 38) - 18) + -1) - -1);
			a196 = ((a398 * a338) - 48);
			a218 = 32;
			a286 = a294[4];
			a270 = 16;
			a361 = 36;
			a353 = a399;
			a358 = a351;
			a302 = a346[2];
			a307 = a227[2];
			a329 = 36;
			a383 = a226[7];
			a382 = ((((a382 - 6241) % 107) - -164) + 8);
			a300 = 0;
			a230 = 4;
			a392 = a304;
			a338 = 5;
			a202 = a217[1];
			a134 = 1;
			a333 = (((((a333 / 5) * 5) - 16386) * -1) / 10);
			a249 = ((((a249 + -12339) % 71) + 449) - -6);
			a276 = a250;
			a378 = 0;
			a359 = 9;
			a225 = a205[7];
			a373 = 0;
			a75 = 35;
			a339 = 0;
			a243 = ((((((a243 - -16864) % 43) + -127) * 5) % 43) + -110);
			a240 = 0;
			a235 = a216[4];
			a313 = 35;
			a265 = a376;
			a207 = 34;
			a54 = ((((50 / 5) * 5) / 5) + 310);
			a324 = a232[6];
			a237 = 7;
			a256 = 36;
			a395 = 0;
			a269 = 35;
			a260 = 0;
			a320 = 7;
			a201 = ((((48 - -10112) - 10289) * 9) / 10);
			a296 = a384;
			a336 = 0;
			a206 = 11;
			a370 = a311;
			a386 = (((a386 * 5) - -24177) / 5);
			a239 = a268;
			a228 = a264;
			a277 = ((((((a277 % 95) - -158) * 10) / 9) * 9) / 10);
			a234 = a372[2];
			a224 = 34;
			a398 = 15;
		} else {
			a155 = 34;
			a75 = 33;
			a132 = 0;
			a77 = ((a338 * a270) - 53);
		}
	}
	if ((((a295 == a366[4] && ((a300 == 1 && ((((a57 == 13 && cf == 1) && a75 == 34) && (26 == a137[1])) && (77 == a358[0]))) && (47 == a239[4]))) && a235 == a216[2]) && ((a383 == a226[2] && a324 == a232[2]) && input == inputs[8]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a162 -= (a162 - 20) < a162 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a286 = a294[3];
		a295 = a366[(a338 + -5)];
		a333 = (((((a333 * -1) / 10) + -6) - -25046) + -24962);
		a211 = 8;
		a296 = a384;
		a383 = a226[5];
		a320 = 11;
		a353 = a399;
		a134 = 0;
		a218 = 36;
		a277 = (((((a277 / 5) * 10) / 9) - -28994) + -28932);
		a359 = 6;
		a276 = a289;
		a338 = 8;
		a225 = a205[4];
		a398 = 14;
		a75 = 35;
		a269 = 35;
		a265 = a376;
		a358 = a351;
		a370 = a318;
		a392 = a304;
		a329 = 35;
		a386 = (((((a386 * 17) / 10) / 5) + -896) + 11515);
		a202 = a217[5];
		a310 = (((((a310 * 5) / 5) + 14119) % 20) - -332);
		a368 = 0;
		a336 = 0;
		a224 = 35;
		a239 = a268;
		a339 = 0;
		a378 = 0;
		a201 = ((((9 / 5) * 5) * 9) / 10);
		a228 = a292;
		a196 = (a57 + 3);
	}
	if (((input == inputs[2] && (a57 == 13 && ((110 == a276[2]) && ((cf == 1 && a75 == 34) && a295 == a366[4])))) && ((((316 < a310) && (357 >= a310)) && (a313 == 34 && ((a211 == 3 && ((147 < a333) && (177 >= a333))) && a302 == a346[2]))) && (26 == a137[1])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a174 += (a174 + 20) > a174 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		cf = 0;
		if ((a59 == 34 && (a373 == 1 || a395 != 1))) {
			a173 = 34;
			a107 = 34;
			a75 = 32;
			a172 = a320;
		} else {
			a392 = a304;
			a286 = a294[0];
			a338 = 10;
			a302 = a346[2];
			a173 = 32;
			a240 = 1;
			a395 = 1;
			a370 = a318;
			a357 = (((a357 / 5) * 5) - -13625);
			a75 = 32;
			a329 = 36;
			a313 = 35;
			a276 = a253;
			a382 = (((a382 - 23027) - 6534) + -350);
			a225 = a205[0];
			a129 = a92[((a230 * a206) - 29)];
			a324 = a232[2];
			a235 = a216[7];
			a125 = a30[(a270 + -5)];
			a310 = ((((a310 - -16662) * 10) / 9) * 1);
			a270 = 16;
			a361 = 36;
			a307 = a227[4];
			a230 = 9;
		}
	}
	if (((((26 == a137[1]) && (a218 == 34 && (a234 == a372[2] && (a240 == 1 && ((a235 == a216[2] && (a295 == a366[4] && (a75 == 34 && cf == 1))) && a260 == 1))))) && a57 == 13) && (input == inputs[1] && a300 == 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a72 = ((((90 * 10) / -8) * 5) - 11773);
		a57 = (a211 - -12);
		a141 = a47[(a230 - -2)];
	}
	if (((a225 == a205[2] && ((a313 == 34 && a57 == 13) && (38 == a370[4]))) && (a339 != 1 && (a307 == a227[2] && (a269 == 34 && (a295 == a366[4] && ((a75 == 34 && ((26 == a137[1]) && cf == 1)) && input == inputs[7]))))))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		cf = 0;
		a75 = 32;
		a125 = a30[(a57 + -12)];
		a173 = 32;
		a8 = (a57 - 1);
	}
}
void calculate_outputm145(int input) {
	if (((a323 == 7 && ((a383 == a226[2] && ((cf == 1 && a57 == 13) && input == inputs[9])) && a270 == 12)) && (((((31 == a137[0]) && (a307 == a227[2] && a234 == a372[2])) && (56 == a265[2])) && a75 == 34) && ((148 < a277) && (339 >= a277))))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 2 : 0;
		a5 += (a5 + 20) > a5 ? 2 : 0;
		a93 += (a93 + 20) > a93 ? 2 : 0;
		a94 -= (a94 - 20) < a94 ? 4 : 0;
		cf = 0;
		a333 = (((((a333 * a249) % 14999) + -28538) + -331) * 1);
		a225 = a205[(a237 + -5)];
		a300 = 1;
		a230 = (a237 + -2);
		a339 = 1;
		a395 = 1;
		a146 = 0;
		a265 = a376;
		a324 = a232[(a359 - a359)];
		a16 = 1;
		a383 = a226[(a323 + -7)];
		a256 = 34;
		a378 = 1;
		a211 = (a237 - 3);
		a201 = ((((((a201 * a243) + 26723) % 93) - 105) / 5) - 155);
		a392 = a257;
		a75 = 36;
		a277 = (((((a310 * a249) % 14999) + 3704) - 26533) * 1);
		a269 = 32;
		a260 = 1;
		a234 = a372[(a359 - 3)];
		a243 = (((((a333 * a333) % 14999) + -29456) + -80) / 5);
		a307 = a227[((a338 * a359) + -24)];
		a386 = (((((a386 * a333) % 14999) + -8820) - 2639) * 1);
		a240 = 1;
		a218 = 33;
		a368 = 1;
		a329 = 33;
		a373 = 1;
		a270 = (a57 + -3);
		a353 = a263;
		a276 = a250;
		a286 = a294[((a359 / a359) + 1)];
		a320 = (a237 - -2);
		a228 = a229;
		a235 = a216[(a237 - a237)];
		a338 = (a359 - 2);
		a313 = 32;
		a302 = a346[(a323 - 5)];
		a357 = ((((a357 * a310) + -2241) / 5) - 19146);
		a398 = (a323 - -3);
		a249 = (((((((a277 * a333) % 14999) + 11100) % 71) - -363) * 10) / 9);
		a310 = ((((((a310 * a277) % 14999) % 77) - -237) + 0) * 1);
		a206 = (a359 + -1);
		a358 = a348;
		a237 = (a359 - 2);
		a202 = a217[((a359 + a230) + -7)];
		a361 = 33;
		a336 = 1;
		a207 = 33;
		a224 = 34;
		a359 = (a230 - -2);
		a239 = a242;
		a73 = (((25 - 26382) * 1) - -26528);
	}
	if ((((((355 < a249) && (499 >= a249)) && a234 == a372[2]) && (input == inputs[8] && (a57 == 13 && ((15 == a353[2]) && (((31 == a137[0]) && ((a338 == 5 && (a323 == 7 && (cf == 1 && a75 == 34))) && a260 == 1)) && (56 == a265[2])))))) && a174 <= 3)) {
		a164 += (a164 + 20) > a164 ? 1 : 0;
		cf = 0;
		a201 = ((((((a201 * a243) / 5) - 17005) / 5) % 93) - 96);
		a329 = 32;
		a270 = (a211 + 8);
		a307 = a227[(a211 - 2)];
		a240 = 0;
		a125 = a30[a323];
		a357 = ((((((a357 * a277) * 1) % 65) + -121) - 2945) - -2943);
		a276 = a289;
		a392 = a257;
		a338 = (a57 + -9);
		a313 = 32;
		a129 = a92[(a323 + -6)];
		a230 = (a237 + -1);
		a173 = 32;
		a75 = 32;
		a310 = ((((((a310 * a201) % 14999) % 77) - -238) / 5) + 240);
	}
	if ((((a368 == 1 && (((-156 < a243) && (-68 >= a243)) && ((a260 == 1 && a57 == 13) && a240 == 1))) && (a323 == 7 && (a230 == 5 && (a206 == 6 && ((31 == a137[0]) && ((cf == 1 && input == inputs[0]) && a75 == 34)))))) && a63 >= 3)) {
		a51 += (a51 + 20) > a51 ? 1 : 0;
		cf = 0;
		a395 = 1;
		a183 = 35;
		a370 = a311;
		a312 = 34;
		a57 = (a211 - -13);
		a278 = a326[a230];
	}
	if (((((a206 == 6 && (a75 == 34 && (a234 == a372[2] && ((cf == 1 && a57 == 13) && input == inputs[1])))) && a368 == 1) && (a398 == 12 && ((((31 == a137[0]) && a230 == 5) && a323 == 7) && (59 == a228[3])))) && a165 == 4790)) {
		cf = 0;
		a72 = (((((a386 * a386) % 14999) + -25817) / 5) * 5);
		a141 = a47[((a57 / a57) - -1)];
		a57 = ((a206 + a323) - -2);
	}
	if ((((a270 == 12 && (a269 == 34 && ((a57 == 13 && cf == 1) && (31 == a137[0])))) && ((((a75 == 34 && ((110 == a276[2]) && (a323 == 7 && a339 != 1))) && ((148 < a277) && (339 >= a277))) && a329 == 34) && input == inputs[4])) && a89 == 9776)) {
		a5 -= (a5 - 20) < a5 ? 1 : 0;
		cf = 0;
		a8 = (a237 + 1);
		a75 = 32;
		a173 = 34;
		a172 = (a398 + -10);
	}
	if ((((110 == a276[2]) && ((59 == a228[3]) && ((a218 == 34 && (((50 == a392[4]) && (((a323 == 7 && cf == 1) && a57 == 13) && a75 == 34)) && (31 == a137[0]))) && input == inputs[2]))) && (((316 < a310) && (357 >= a310)) && (77 == a358[0])))) {
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a174 += (a174 + 20) > a174 ? 1 : 0;
		cf = 0;
		a228 = a229;
		a302 = a346[(a211 - 1)];
		a370 = a318;
		a235 = a216[(a206 - 4)];
		a361 = 34;
		a200 = a115[(a398 - 7)];
		a395 = 1;
		a225 = a205[((a398 * a338) - 58)];
		a158 = (a57 - 8);
		a312 = 34;
		a202 = a217[(a338 - 3)];
		a57 = ((a158 / a158) + 9);
		a382 = (((((a243 * a333) + -299) % 107) + 164) - -12);
		a286 = a294[(a323 - 5)];
		a276 = a253;
		a324 = a232[(a206 + -4)];
		a296 = a362;
		a320 = ((a338 - a338) - -8);
	}
	if ((((((110 == a276[2]) && ((148 < a277) && (339 >= a277))) && (15 == a353[2])) && a383 == a226[2]) && (((147 < a333) && (177 >= a333)) && ((((a368 == 1 && (((31 == a137[0]) && cf == 1) && a57 == 13)) && a75 == 34) && a323 == 7) && input == inputs[5])))) {
		a131 += (a131 + 20) > a131 ? 2 : 0;
		a169 += (a169 + 20) > a169 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 2 : 0;
		a90 += (a90 + 20) > a90 ? 6 : 0;
		a110 += (a110 + 20) > a110 ? 2 : 0;
		a31 -= (a31 - 20) < a31 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 2 : 0;
		cf = 0;
		a296 = a362;
		a324 = a232[((a359 + a323) + -10)];
		a277 = (((((((a277 * a201) % 14999) * 2) % 95) - -244) / 5) - -145);
		a243 = (((((a243 * a201) % 11) + -166) + -2) * 1);
		a300 = 0;
		a312 = 34;
		a256 = 32;
		a361 = 34;
		a302 = a346[(a359 + -3)];
		a235 = a216[((a211 * a206) + -17)];
		a382 = (((((((a333 * a386) % 14999) % 107) - -38) * 5) % 107) - 32);
		a137 = a189;
		a370 = a311;
		a395 = 1;
		a378 = 0;
		a201 = ((((((a201 * a249) % 14999) % 93) - 104) - 3539) - -3538);
		a320 = ((a398 + a270) + -16);
		a225 = a205[(a270 - 10)];
		a286 = a294[(a206 - 4)];
		a310 = (((((((a310 * a382) % 14999) % 77) + 238) - 1) + 25263) + -25260);
		a154 = ((a359 - a237) + 16);
		a269 = 32;
		a202 = a217[((a206 + a206) - 10)];
		a383 = a226[((a206 * a398) - 70)];
	}
	if ((((((input == inputs[6] && cf == 1) && (31 == a137[0])) && (50 == a392[4])) && a224 == 34) && (((a383 == a226[2] && (a57 == 13 && ((a240 == 1 && a323 == 7) && a75 == 34))) && a378 == 1) && a307 == a227[2]))) {
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		cf = 0;
		a75 = 35;
		a310 = (((((a310 * a249) % 14999) - 25437) + -3500) / 5);
		a184 = a157[((a398 * a206) - 69)];
		a307 = a227[((a270 + a320) - 18)];
		a228 = a229;
		a339 = 1;
		a276 = a253;
		a218 = 33;
		a358 = a348;
		a373 = 1;
		a378 = 1;
		a295 = a366[((a270 + a359) + -13)];
		a224 = 33;
		a359 = (a57 + -10);
		a336 = 1;
		a207 = 33;
		a202 = a217[((a323 + a320) + -13)];
		a201 = ((((((a201 * a386) % 14999) % 14900) + -15098) + -2) + 0);
		a269 = 33;
		a134 = 0;
		a333 = ((((((a333 * a277) % 14999) - -10863) * 1) * 10) / -9);
	}
}
void calculate_outputm146(int input) {
	if (((a312 == 34 && ((a235 == a216[2] && (47 == a239[4])) && a57 == 13)) && (((((((355 < a249) && (499 >= a249)) && ((cf == 1 && input == inputs[5]) && (31 == a137[0]))) && a313 == 34) && a75 == 34) && a323 == 10) && a312 == 34))) {
		a67 -= (a67 - 20) < a67 ? 1 : 0;
		cf = 0;
		if ((a235 == a216[4] || !(23 == a274[2]))) {
			a320 = (a230 - -3);
			a370 = a285;
			a260 = 1;
			a382 = (((((a249 * a357) % 107) + 69) - -25625) + -25624);
			a256 = 33;
			a395 = 1;
			a201 = (((((((a357 * a357) % 94) + 84) * 5) * 5) % 94) - -82);
			a243 = ((((((a277 * a382) % 14999) % 43) + -110) + 29982) - 29983);
			a235 = a216[((a398 * a398) + -144)];
			a338 = a237;
			a378 = 1;
			a154 = (a211 - -9);
			a361 = 34;
			a300 = 1;
			a359 = (a206 + -1);
			a296 = a212;
			a265 = a376;
			a392 = a257;
			a234 = a372[((a230 + a323) + -13)];
			a286 = a294[((a338 * a323) - 48)];
			a386 = ((((((((a243 * a249) % 14999) % 61) - -263) + -1) * 5) % 61) - -260);
			a137 = a189;
			a202 = a217[(a237 + -3)];
			a206 = (a398 - 8);
			a310 = ((((((a333 * a333) % 14999) % 77) + 203) + 19) + -33);
			a373 = 0;
			a270 = ((a237 * a230) - 13);
			a225 = a205[(a398 - 12)];
			a211 = (a237 + -4);
			a224 = 32;
			a249 = (((((a333 * a333) % 14999) + 13097) - 28485) * 1);
			a230 = ((a359 * a57) - 60);
			a237 = (a398 - 9);
		} else {
			a286 = a294[(a211 - a211)];
			a310 = ((((a357 * a357) + -23810) / 5) * 5);
			a370 = a318;
			a224 = 33;
			a243 = ((((((a357 * a310) % 14999) - -6358) % 14910) - 15088) - 2);
			a358 = a348;
			a99 = a26[(a57 - 6)];
			a359 = a211;
			a235 = a216[((a211 * a323) - 30)];
			a132 = 0;
			a338 = a211;
			a300 = 1;
			a277 = ((((((a277 * a243) % 14999) / 5) / 5) % 78) - -68);
			a230 = a359;
			a225 = a205[((a206 + a57) + -19)];
			a240 = 1;
			a77 = ((a237 / a237) - -10);
			a353 = a263;
			a239 = a242;
			a228 = a229;
			a307 = a227[(a230 + -3)];
			a276 = a253;
			a202 = a217[((a211 + a211) + -6)];
			a75 = 33;
			a218 = 33;
			a312 = 33;
			a382 = ((((((a243 * a357) % 14999) + -4301) % 107) - -69) + -1);
			a249 = (((((a249 * a243) % 14999) + -10815) * 1) / 5);
			a398 = (a211 + 8);
			a234 = a372[((a338 * a338) + -9)];
			a368 = 1;
			a206 = (a323 - 6);
			a270 = a323;
			a207 = 32;
			a386 = (((((((a357 * a243) % 14999) % 61) - -263) + 1) + 24229) - 24229);
			a313 = 33;
			a237 = (a320 - a359);
			a211 = (a320 - 5);
		}
	}
	if (((input == inputs[0] && ((77 == a358[0]) && a324 == a232[2])) && (a230 == 5 && ((((a57 == 13 && (a75 == 34 && ((cf == 1 && a323 == 10) && (31 == a137[0])))) && (110 == a276[2])) && a398 == 12) && (92 == a296[2]))))) {
		a67 -= (a67 - 20) < a67 ? 4 : 0;
		cf = 0;
		a313 = 32;
		a269 = 34;
		a249 = (((((a249 * a382) % 14999) / 5) + -2008) + -13218);
		a206 = ((a359 + a338) - 3);
		a211 = (a237 - 3);
		a270 = (a359 + 7);
		a230 = (a211 + 2);
		a361 = 33;
		a218 = 34;
		a312 = 34;
		a173 = 32;
		a265 = a303;
		a300 = 1;
		a240 = 0;
		a324 = a232[((a338 * a230) - 15)];
		a329 = 34;
		a353 = a241;
		a339 = 0;
		a395 = 0;
		a320 = ((a398 + a338) - 10);
		a207 = 32;
		a224 = 32;
		a8 = (a323 - -1);
		a225 = a205[(a57 + -12)];
		a368 = 1;
		a260 = 0;
		a333 = ((((((a243 * a357) + 18423) + -44436) + -218) % 14) - -169);
		a357 = ((((((a357 * a310) % 65) - 121) + -1) + 4694) - 4694);
		a125 = a30[(a8 + -10)];
		a307 = a227[(a237 + -3)];
		a373 = 1;
		a378 = 1;
		a239 = a299;
		a336 = 1;
		a256 = 33;
		a75 = 32;
		a398 = (a338 - -7);
		a358 = a351;
		a228 = a264;
		a237 = a230;
		a276 = a289;
		a235 = a216[((a323 * a359) - 40)];
		a296 = a384;
		a302 = a346[((a323 - a270) - -2)];
		a277 = (((((((a277 * a201) % 14999) % 78) + 69) - -21006) + -5874) - 15131);
	}
}
void calculate_outputm11(int input) {
	if (((a312 == 34 && ((a359 == 5 && ((147 < a333) && (177 >= a333))) && (110 == a276[2]))) && (a324 == a232[2] && (a240 == 1 && (cf == 1 && (20 == a137[1])))))) {
		if ((((38 == a370[4]) && ((77 == a358[0]) && (a302 == a346[2] && ((a154 == 10 && cf == 1) && (92 == a296[2]))))) && (((148 < a277) && (339 >= a277)) && ((-12 < a201) && (178 >= a201))))) {
			calculate_outputm138(input);
		}
		if ((((a240 == 1 && ((316 < a310) && (357 >= a310))) && a237 == 5) && (((-57 < a357) && (20 >= a357)) && (a338 == 5 && ((50 == a392[4]) && (cf == 1 && a154 == 11)))))) {
			calculate_outputm139(input);
		}
		if (((cf == 1 && a154 == 12) && ((((77 == a358[0]) && (((148 < a277) && (339 >= a277)) && (a234 == a372[2] && a339 != 1))) && a313 == 34) && a395 == 1))) {
			calculate_outputm140(input);
		}
		if ((((a368 == 1 && a338 == 5) && a336 == 1) && (((-39 < a382) && (176 >= a382)) && (((92 == a296[2]) && (a154 == 15 && cf == 1)) && ((201 < a386) && (325 >= a386)))))) {
			calculate_outputm141(input);
		}
		if (((a286 == a294[2] && (a154 == 16 && cf == 1)) && (((59 == a228[3]) && (a240 == 1 && (a313 == 34 && a260 == 1))) && a324 == a232[2]))) {
			calculate_outputm142(input);
		}
	}
	if ((((((26 == a137[1]) && cf == 1) && a336 == 1) && a206 == 6) && ((15 == a353[2]) && ((((-39 < a382) && (176 >= a382)) && ((-156 < a243) && (-68 >= a243))) && a207 == 34)))) {
		if (((a218 == 34 && ((a256 == 34 && ((355 < a249) && (499 >= a249))) && (92 == a296[2]))) && (a224 == 34 && (a368 == 1 && (cf == 1 && a295 == a366[2]))))) {
			calculate_outputm143(input);
		}
		if (((((cf == 1 && a295 == a366[4]) && a225 == a205[2]) && a329 == 34) && ((a256 == 34 && (a260 == 1 && (77 == a358[0]))) && a324 == a232[2]))) {
			calculate_outputm144(input);
		}
	}
	if (((a207 == 34 && (a206 == 6 && ((31 == a137[0]) && cf == 1))) && (a270 == 12 && ((15 == a353[2]) && (a224 == 34 && a313 == 34))))) {
		if (((a373 != 1 && (a329 == 34 && a206 == 6)) && ((a240 == 1 && ((15 == a353[2]) && (a323 == 7 && cf == 1))) && ((-12 < a201) && (178 >= a201))))) {
			calculate_outputm145(input);
		}
		if (((((148 < a277) && (339 >= a277)) && (((a225 == a205[2] && (cf == 1 && a323 == 10)) && a300 == 1) && ((355 < a249) && (499 >= a249)))) && (a302 == a346[2] && a224 == 34))) {
			calculate_outputm146(input);
		}
	}
}
void calculate_outputm152(int input) {
	if (((((((-39 < a382) && (176 >= a382)) && (a338 == 5 && (((a72 <= -104 && cf == 1) && a57 == 15) && a141 == a47[3]))) && a75 == 34) && (15 == a353[2])) && (((a307 == a227[2] && a373 != 1) && ((355 < a249) && (499 >= a249))) && input == inputs[2]))) {
		cf = 0;
		a230 = ((a237 * a237) + -22);
		a353 = a263;
		a361 = 33;
		a333 = (((((a333 * a72) % 14999) - 3263) * 1) / 5);
		a378 = 1;
		a382 = ((((a382 * a357) - 11048) - 2188) - 5781);
		a260 = 1;
		a395 = 1;
		a373 = 1;
		a276 = a253;
		a249 = (((((a249 * a357) % 15076) + -14923) - 0) + -2);
		a295 = a366[((a57 / a57) + 6)];
		a201 = ((((a201 * a357) - 16531) - -42159) - 36696);
		a269 = 33;
		a324 = a232[((a270 * a230) + -34)];
		a300 = 1;
		a228 = a229;
		a211 = a230;
		a235 = a216[(a398 - 10)];
		a320 = (a270 + -6);
		a218 = 33;
		a237 = ((a270 * a398) + -117);
		a296 = a362;
		a206 = (a270 - 8);
		a336 = 1;
		a240 = 1;
		a210 = 1;
		a307 = a227[(a270 + -10)];
		a392 = a208;
		a265 = a303;
		a313 = 33;
		a370 = a318;
		a256 = 33;
		a234 = a372[(a270 - 12)];
		a338 = (a398 - 7);
		a75 = 35;
		a310 = (((((a277 * a386) % 14999) / 5) + -2946) / 5);
		a207 = 32;
		a357 = ((((((a357 * a382) % 14999) % 38) - 18) - -1) + -1);
		a134 = 0;
		a270 = (a359 + 7);
	}
	if ((((50 == a392[4]) && (a141 == a47[3] && (((cf == 1 && a57 == 15) && a75 == 34) && ((-39 < a382) && (176 >= a382))))) && (((((a234 == a372[2] && a72 <= -104) && a270 == 12) && input == inputs[8]) && (56 == a265[2])) && a230 == 5))) {
		a67 -= (a67 - 20) < a67 ? 3 : 0;
		cf = 0;
		a338 = (a237 + -1);
		a277 = (((((((a333 * a249) % 14999) / 5) - 19363) + 21474) % 95) + 231);
		a202 = a217[(a230 - 4)];
		a201 = ((((((a201 * a243) * 1) % 93) + -105) + 20426) + -20426);
		a373 = 1;
		a137 = a117;
		a368 = 1;
		a265 = a303;
		a269 = 33;
		a57 = 13;
		a243 = (((((((a243 * a382) % 11) + -167) * 5) * 5) % 11) + -165);
		a382 = ((((((a382 * a357) % 12) - 50) + 13817) / 5) + -2802);
		a395 = 1;
		a239 = a268;
		a225 = a205[(a270 + -10)];
		a386 = ((((((a333 * a357) / 5) + -4340) / 5) % 61) + 159);
		a339 = 0;
		a359 = (a206 + -2);
		a378 = 1;
		a361 = 33;
		a329 = 34;
		a260 = 1;
		a398 = ((a206 - a320) - -14);
		a323 = (a57 - 3);
		a224 = 34;
		a312 = 34;
		a358 = a335;
		a333 = ((((((a357 * a277) / 5) - 22314) / 5) % 14) - -176);
		a392 = a257;
		a234 = a372[((a398 - a398) + 1)];
		a256 = 33;
		a320 = (a230 + 1);
	}
}
void calculate_outputm13(int input) {
	if (((((-12 < a201) && (178 >= a201)) && ((-156 < a243) && (-68 >= a243))) && (((a373 != 1 && ((a72 <= -104 && cf == 1) && a269 == 34)) && ((147 < a333) && (177 >= a333))) && ((-57 < a357) && (20 >= a357))))) {
		if (((a378 == 1 && (((((92 == a296[2]) && a313 == 34) && (59 == a228[3])) && a237 == 5) && a336 == 1)) && (cf == 1 && a141 == a47[3]))) {
			calculate_outputm152(input);
		}
	}
}
void calculate_outputm159(int input) {
	if (((((a269 == 34 && a269 == 34) && a260 == 1) && a278 == a326[3]) && ((110 == a276[2]) && ((a225 == a205[2] && (a57 == 16 && (((cf == 1 && a184 == a157[2]) && a75 == 34) && a338 == 5))) && input == inputs[5])))) {
		a131 += (a131 + 20) > a131 ? 2 : 0;
		a169 += (a169 + 20) > a169 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 2 : 0;
		a90 += (a90 + 20) > a90 ? 6 : 0;
		a110 += (a110 + 20) > a110 ? 2 : 0;
		a31 -= (a31 - 20) < a31 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 2 : 0;
		a122 -= (a122 - 20) < a122 ? 4 : 0;
		cf = 0;
		a243 = (((((a277 * a357) % 11) - 167) - -4748) - 4747);
		a57 = (a338 + 8);
		a313 = 34;
		a383 = a226[(a270 / a237)];
		a137 = a189;
		a324 = a232[(a320 + -6)];
		a269 = 32;
		a154 = (a359 - -11);
		a256 = 32;
		a277 = (((((((a277 * a382) % 14999) % 95) - -243) - 0) / 5) + 151);
		a310 = ((((((a310 * a386) % 14999) % 77) + 168) / 5) + 239);
		a300 = 0;
		a207 = 34;
		a392 = a304;
		a228 = a292;
		a202 = a217[((a398 + a230) - 15)];
		a378 = 0;
		a235 = a216[(a211 + -2)];
	}
	if (((((a240 == 1 && ((a336 == 1 && a234 == a372[2]) && (77 == a358[0]))) && input == inputs[9]) && a75 == 34) && (a278 == a326[3] && ((((a57 == 16 && cf == 1) && a184 == a157[2]) && a336 == 1) && a206 == 6)))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 2 : 0;
		a5 += (a5 + 20) > a5 ? 2 : 0;
		a93 += (a93 + 20) > a93 ? 2 : 0;
		a94 -= (a94 - 20) < a94 ? 4 : 0;
		cf = 0;
		a16 = 1;
		a383 = a226[(a359 - 5)];
		a243 = (((48 - 11616) + 8710) * 5);
		a333 = ((((((a243 * a243) % 14999) - -8293) * 1) * -1) / 10);
		a338 = (a57 - 13);
		a370 = a285;
		a269 = 32;
		a224 = 34;
		a398 = (a320 + 2);
		a300 = 1;
		a357 = ((((((a357 * a249) % 14906) + -15093) + 23823) * 1) - 23823);
		a312 = 33;
		a206 = (a320 - 4);
		a237 = (a320 - 5);
		a73 = ((((((((a277 * a382) % 14999) % 54) + 221) * 5) + -8088) % 54) + 271);
		a256 = 34;
		a310 = (((((((a310 * a357) % 14999) + 11653) * 2) - -6430) % 77) - -238);
		a361 = 33;
		a358 = a348;
		a373 = 1;
		a329 = 33;
		a225 = a205[(a206 - 4)];
		a336 = 1;
		a240 = 1;
		a260 = 1;
		a386 = (((((a333 * a243) % 14999) - 4353) + -17231) / 5);
		a368 = 1;
		a286 = a294[(a338 - 1)];
		a324 = a232[((a359 / a359) + -1)];
		a249 = (((((((a243 * a73) % 14999) - 6913) % 71) - -458) + 4673) - 4647);
		a307 = a227[(a206 + -3)];
		a277 = (((((a333 * a333) % 14999) - 28371) + -186) - 1045);
		a339 = 1;
		a234 = a372[(a230 - 3)];
		a353 = a263;
		a75 = 36;
		a270 = (a211 + 7);
		a382 = ((((((a386 * a333) % 14999) - -14133) + -5959) % 12) + -51);
		a239 = a242;
		a265 = a376;
		a302 = a346[(a206 - 2)];
		a230 = (a320 - 5);
		a146 = 0;
		a211 = (a338 + -1);
		a235 = a216[(a320 - 8)];
		a276 = a250;
		a296 = a212;
		a395 = 1;
		a202 = a217[(a398 - 9)];
		a320 = (a359 + 2);
		a218 = 33;
		a359 = (a398 - 5);
	}
	if (((((a224 == 34 && (a75 == 34 && (cf == 1 && input == inputs[4]))) && (15 == a353[2])) && (((147 < a333) && (177 >= a333)) && (a278 == a326[3] && ((110 == a276[2]) && (a57 == 16 && (a184 == a157[2] && (a218 == 34 && a286 == a294[2]))))))) && a89 == 9776)) {
		cf = 0;
		a172 = (a237 - 3);
		a173 = 34;
		a75 = 32;
		a8 = (a237 - -1);
	}
	if ((((((148 < a277) && (339 >= a277)) && ((a75 == 34 && (((92 == a296[2]) && a300 == 1) && a286 == a294[2])) && a184 == a157[2])) && (a57 == 16 && (((input == inputs[1] && (a278 == a326[3] && cf == 1)) && ((-57 < a357) && (20 >= a357))) && a269 == 34))) && a165 == 4790)) {
		a168 += (a168 + 20) > a168 ? 4 : 0;
		cf = 0;
		a72 = ((((36 * -29) / 10) - 11644) - 4894);
		a141 = a47[((a270 - a270) - -2)];
		a57 = (a398 - -3);
	}
	if ((((input == inputs[0] && (a75 == 34 && ((((355 < a249) && (499 >= a249)) && a373 != 1) && a320 == 8))) && (((148 < a277) && (339 >= a277)) && (((148 < a277) && (339 >= a277)) && ((a278 == a326[3] && ((cf == 1 && a57 == 16) && a184 == a157[2])) && a300 == 1)))) && a63 >= 3)) {
		a174 += (a174 + 20) > a174 ? 2 : 0;
		cf = 0;
		a183 = 35;
		a228 = a292;
		a392 = a304;
		a278 = a326[(a270 + -7)];
	}
	if ((((a218 == 34 && ((a278 == a326[3] && (a224 == 34 && (a206 == 6 && input == inputs[8]))) && a240 == 1)) && (a329 == 34 && (a373 != 1 && (((a75 == 34 && cf == 1) && a184 == a157[2]) && a57 == 16)))) && a174 <= 3)) {
		a162 -= (a162 - 20) < a162 ? 3 : 0;
		cf = 0;
		a230 = ((a57 / a359) - -1);
		a329 = 32;
		a240 = 0;
		a129 = a92[(a359 - 4)];
		a307 = a227[(a230 - 3)];
		a173 = 32;
		a125 = a30[((a237 + a320) + -6)];
		a370 = a285;
		a357 = (((((a357 * a333) - 9546) % 65) + -84) - -15);
		a338 = (a57 - 12);
		a75 = 32;
		a395 = 0;
		a276 = a289;
		a382 = (((((((a382 * a249) % 14999) - -7478) - 8424) - 11164) % 12) + -52);
		a270 = ((a398 - a359) + 4);
		a286 = a294[((a338 / a206) - -1)];
		a361 = 32;
		a225 = a205[((a230 + a211) - 6)];
		a310 = ((((((a310 * a277) % 14999) + -1100) % 77) - -238) * 1);
		a302 = a346[((a57 / a359) + -2)];
	}
	if (((a57 == 16 && (a302 == a346[2] && ((((15 == a353[2]) && a269 == 34) && a278 == a326[3]) && a211 == 3))) && (((((input == inputs[2] && cf == 1) && a184 == a157[2]) && a269 == 34) && a75 == 34) && a336 == 1))) {
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		cf = 0;
		a201 = (((((((a382 * a310) % 14999) % 94) - -83) - -1) - 16607) - -16607);
		a276 = a253;
		a324 = a232[(a338 + -3)];
		a202 = a217[(a230 - 3)];
		a158 = (a57 - 11);
		a370 = a318;
		a207 = 34;
		a200 = a115[((a230 + a158) + -5)];
		a392 = a304;
		a313 = 34;
		a57 = (a270 + -2);
		a378 = 1;
		a235 = a216[(a206 - 4)];
	}
	if ((((a361 == 34 && (input == inputs[6] && ((((148 < a277) && (339 >= a277)) && a278 == a326[3]) && a184 == a157[2]))) && a339 != 1) && ((a302 == a346[2] && (a368 == 1 && ((a57 == 16 && cf == 1) && a75 == 34))) && a300 == 1))) {
		a120 -= (a120 - 20) < a120 ? 3 : 0;
		cf = 0;
		a336 = 1;
		a295 = a366[(a57 - 12)];
		a184 = a157[(a398 - 9)];
		a75 = 35;
		a201 = (((((a333 * a382) % 14999) / 5) / 5) - 13715);
		a296 = a212;
		a320 = (a230 - -1);
		a202 = a217[(a211 + -3)];
		a373 = 1;
		a339 = 1;
		a307 = a227[(a359 - 5)];
		a276 = a253;
		a269 = 33;
		a310 = ((((((a310 * a249) % 14999) - 23789) * 1) + 25004) * -1);
		a358 = a348;
		a218 = 33;
		a359 = (a320 - 3);
		a312 = 33;
		a224 = 33;
		a134 = 0;
		a333 = ((((((a333 * a310) % 14999) - -14365) % 14976) + -15022) * 1);
	}
}
void calculate_outputm164(int input) {
	if (((((a57 == 16 && (((a81 == a167[0] && cf == 1) && input == inputs[6]) && a278 == a326[7])) && a373 != 1) && a224 == 34) && (a237 == 5 && (((a235 == a216[2] && a383 == a226[2]) && a75 == 34) && a373 != 1)))) {
		a5 -= (a5 - 20) < a5 ? 2 : 0;
		cf = 0;
		a333 = (((((a277 * a277) % 14999) + -17251) * 1) / 5);
		a218 = 33;
		a359 = a211;
		a202 = a217[(a359 - 3)];
		a224 = 33;
		a75 = 35;
		a201 = ((((((a201 * a333) % 14999) % 14900) - 15098) - 2) + -1);
		a276 = a253;
		a320 = ((a57 + a270) + -22);
		a307 = a227[((a211 - a270) + 9)];
		a184 = a157[(a57 - 13)];
		a295 = a366[((a206 - a237) + 3)];
		a336 = 1;
		a134 = 0;
		a378 = 1;
		a373 = 1;
		a207 = 33;
		a296 = a212;
		a310 = (((((a310 * a357) + -8698) + 18468) * 1) + -18554);
	}
	if ((((a81 == a167[0] && (a278 == a326[7] && ((a75 == 34 && cf == 1) && a57 == 16))) && ((92 == a296[2]) && (((a230 == 5 && (a235 == a216[2] && (input == inputs[8] && ((316 < a310) && (357 >= a310))))) && a395 == 1) && a202 == a217[2]))) && a174 <= 3)) {
		cf = 0;
		a270 = (a320 + 3);
		a225 = a205[((a237 - a237) - -1)];
		a338 = (a359 - 1);
		a357 = ((((((a357 * a333) - 9625) % 65) - 90) / 5) + -113);
		a75 = 32;
		a313 = 32;
		a230 = (a359 - 1);
		a202 = a217[(a206 - 5)];
		a395 = 0;
		a129 = a92[(a57 / a57)];
		a286 = a294[((a320 * a320) + -63)];
		a235 = a216[(a206 + -5)];
		a307 = a227[(a270 + -10)];
		a125 = a30[(a359 + 2)];
		a302 = a346[(a338 - 3)];
		a361 = 32;
		a324 = a232[(a206 - 5)];
		a329 = 32;
		a392 = a257;
		a240 = 0;
		a173 = 32;
		a201 = ((((((a201 * a310) % 14999) % 93) + -105) - -1) + -2);
		a310 = (((((a310 * a382) * 1) * 1) % 77) - -241);
	}
	if (((((a57 == 16 && (a225 == a205[2] && (a278 == a326[7] && (cf == 1 && input == inputs[4])))) && a378 == 1) && ((a207 == 34 && (a75 == 34 && ((a383 == a226[2] && a329 == 34) && a81 == a167[0]))) && a383 == a226[2])) && a89 == 9776)) {
		a31 -= (a31 - 20) < a31 ? 2 : 0;
		cf = 0;
		a75 = 32;
		a172 = ((a57 + a57) - 30);
		a173 = 34;
		a8 = ((a270 / a270) + 5);
	}
	if ((((((-57 < a357) && (20 >= a357)) && (a302 == a346[2] && (input == inputs[0] && ((148 < a277) && (339 >= a277))))) && ((a260 == 1 && (a81 == a167[0] && (a383 == a226[2] && (((cf == 1 && a278 == a326[7]) && a75 == 34) && a57 == 16)))) && (47 == a239[4]))) && a63 >= 3)) {
		a63 -= (a63 - 20) < a63 ? 1 : 0;
		cf = 0;
		a312 = 34;
		a370 = a311;
		a228 = a292;
		a183 = 35;
		a278 = a326[(a57 - 11)];
	}
	if ((((((148 < a277) && (339 >= a277)) && (((input == inputs[9] && cf == 1) && a57 == 16) && a278 == a326[7])) && a207 == 34) && ((a383 == a226[2] && (((a313 == 34 && a361 == 34) && a81 == a167[0]) && a75 == 34)) && a336 == 1))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 4 : 0;
		a56 += (a56 + 20) > a56 ? 2 : 0;
		a5 += (a5 + 20) > a5 ? 2 : 0;
		a93 += (a93 + 20) > a93 ? 2 : 0;
		a94 -= (a94 - 20) < a94 ? 4 : 0;
		cf = 0;
		a146 = 0;
		a270 = (a206 + 4);
		a201 = ((((((a201 * a310) % 14999) + -10983) / 5) % 93) - 105);
		a256 = 34;
		a398 = ((a270 / a270) + 9);
		a395 = 1;
		a378 = 1;
		a320 = (a211 + 4);
		a329 = 33;
		a286 = a294[(a57 - 14)];
		a269 = 32;
		a338 = (a398 + -7);
		a230 = (a398 + -7);
		a296 = a212;
		a373 = 1;
		a202 = a217[((a398 * a270) + -99)];
		a207 = 33;
		a225 = a205[(a398 + -10)];
		a392 = a257;
		a361 = 33;
		a333 = ((((99 / 5) * 5) * -5) / 10);
		a336 = 1;
		a239 = a242;
		a353 = a263;
		a234 = a372[(a57 + -14)];
		a240 = 1;
		a324 = a232[(a230 - 3)];
		a310 = ((((((((a310 * a386) % 14999) - -9881) % 77) - -232) * 5) % 77) - -166);
		a368 = 1;
		a237 = (a359 + -2);
		a218 = 33;
		a224 = 34;
		a243 = (((66 * 5) - 22567) + -2700);
		a260 = 1;
		a73 = (((4 / 5) / 5) - -243);
		a235 = a216[(a398 - 10)];
		a386 = (((((a333 * a243) % 14999) - 18401) / 5) / 5);
		a302 = a346[(a206 / a338)];
		a359 = ((a57 + a270) - 21);
		a307 = a227[(a57 + -15)];
		a75 = 36;
		a300 = 1;
		a313 = 32;
		a277 = (((((a277 * a333) % 14999) - 12025) - -2698) / 5);
		a357 = (((((a357 * a249) + -273) % 14906) + -15093) * 1);
		a249 = ((((((a249 % 71) + 394) * 5) + 596) % 71) + 427);
		a383 = a226[(a211 + -3)];
		a265 = a376;
		a211 = (a206 + -4);
		a276 = a250;
		a16 = 1;
		a206 = (a338 + 1);
	}
	if ((((((201 < a386) && (325 >= a386)) && a278 == a326[7]) && input == inputs[5]) && (((((((a75 == 34 && (cf == 1 && a57 == 16)) && a81 == a167[0]) && (50 == a392[4])) && a202 == a217[2]) && (50 == a392[4])) && ((148 < a277) && (339 >= a277))) && a286 == a294[2]))) {
		a131 += (a131 + 20) > a131 ? 2 : 0;
		a169 += (a169 + 20) > a169 ? 1 : 0;
		a35 += (a35 + 20) > a35 ? 2 : 0;
		a90 += (a90 + 20) > a90 ? 6 : 0;
		a110 += (a110 + 20) > a110 ? 2 : 0;
		a31 -= (a31 - 20) < a31 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 2 : 0;
		a120 += (a120 + 20) > a120 ? 2 : 0;
		cf = 0;
		a370 = a311;
		a312 = 34;
		a276 = a250;
		a269 = 32;
		a339 = 0;
		a300 = 0;
		a228 = a292;
		a358 = a335;
		a57 = (a270 + 1);
		a310 = (((((((a310 * a249) % 14999) - -4600) % 77) + 178) * 10) / 9);
		a382 = (((((a357 * a386) - 11071) + 31650) % 107) + -32);
		a243 = ((((((a277 * a357) - -2422) - -10110) - 15621) % 11) + -167);
		a235 = a216[((a206 - a206) + 1)];
		a137 = a189;
		a277 = (((((((a277 * a357) % 95) + 243) + 0) * 5) % 95) - -182);
		a201 = (((((((a201 * a382) % 14999) % 93) - 104) - -16343) - -2145) - 18489);
		a256 = 32;
		a378 = 0;
		a154 = (a270 + 4);
		a383 = a226[(a230 - 3)];
	}
	if (((((a75 == 34 && (((a373 != 1 && a383 == a226[2]) && a383 == a226[2]) && ((316 < a310) && (357 >= a310)))) && a211 == 3) && a81 == a167[0]) && ((((cf == 1 && input == inputs[2]) && a278 == a326[7]) && ((148 < a277) && (339 >= a277))) && a57 == 16))) {
		a89 += (a89 + 20) > a89 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a67 -= (a67 - 20) < a67 ? 1 : 0;
		cf = 0;
		a339 = 0;
		a269 = 34;
		a276 = a253;
		a312 = 34;
		a57 = (a359 + 5);
		a382 = ((((((((a249 * a249) % 14999) % 107) - -51) * 9) / 10) * 10) / 9);
		a358 = a335;
		a370 = a318;
		a158 = (a57 - 5);
		a200 = a115[(a320 + -3)];
	}
	if ((((input == inputs[1] && (((a278 == a326[7] && (a57 == 16 && cf == 1)) && a324 == a232[2]) && ((201 < a386) && (325 >= a386)))) && (a302 == a346[2] && (((147 < a333) && (177 >= a333)) && (a81 == a167[0] && ((56 == a265[2]) && (a270 == 12 && a75 == 34)))))) && a165 == 4790)) {
		a120 -= (a120 - 20) < a120 ? 1 : 0;
		cf = 0;
		a72 = (((54 + -20094) - 7407) - 2110);
		a141 = a47[(a206 + -4)];
		a57 = (a338 - -10);
	}
}
void calculate_outputm14(int input) {
	if ((((((316 < a310) && (357 >= a310)) && (a278 == a326[3] && cf == 1)) && a336 == 1) && ((a336 == 1 && (a270 == 12 && a256 == 34)) && a307 == a227[2]))) {
		if ((((38 == a370[4]) && (a312 == 34 && ((a336 == 1 && ((-57 < a357) && (20 >= a357))) && a270 == 12))) && ((a184 == a157[2] && cf == 1) && a218 == 34))) {
			calculate_outputm159(input);
		}
	}
	if (((a237 == 5 && ((a202 == a217[2] && ((50 == a392[4]) && (((-12 < a201) && (178 >= a201)) && (cf == 1 && a278 == a326[7])))) && ((316 < a310) && (357 >= a310)))) && a300 == 1)) {
		if (((a313 == 34 && a368 == 1) && ((56 == a265[2]) && (a320 == 8 && (a202 == a217[2] && (((355 < a249) && (499 >= a249)) && (cf == 1 && a81 == a167[0]))))))) {
			calculate_outputm164(input);
		}
	}
}
void calculate_outputm171(int input) {
	if (((input == inputs[6] && ((a240 == 1 && a249 <= 152) && a196 == 10)) && ((((a383 == a226[0] && (((a134 == 1 && cf == 1) && a129 == a92[2]) && a313 == 33)) && a75 == 35) && a207 == 33) && a270 == 10))) {
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		cf = 0;
		if ((!(a313 == 35) || ((a270 == 11 || a132 == 1) && a225 == a205[5]))) {
			a270 = ((a320 * a398) - 49);
			a225 = a205[(a359 - 3)];
			a386 = (((((((a386 * a357) % 14999) - 14814) - 96) - -23026) % 61) + 140);
			a141 = a47[(a320 / a320)];
			a333 = ((((((a333 * a249) % 14999) - -11946) % 14976) + -15022) - 2);
			a269 = 32;
			a42 = (a206 - -4);
			a239 = a242;
			a240 = 0;
			a206 = (a237 - -2);
			a207 = 32;
			a75 = 32;
			a260 = 0;
			a383 = a226[(a398 - 10)];
			a277 = (((((((a277 * a201) % 14999) / 5) / 5) - -5628) % 78) - -58);
			a373 = 1;
			a228 = a229;
			a353 = a263;
			a234 = a372[((a338 * a230) - 9)];
			a320 = (a398 + -3);
			a230 = (a270 + -8);
			a338 = ((a398 * a270) + -107);
			a359 = ((a237 / a196) - -3);
			a312 = 33;
			a313 = 32;
			a237 = ((a398 / a270) - -3);
			a218 = 33;
			a300 = 1;
			a276 = a289;
			a211 = (a398 + -9);
			a173 = 36;
			a398 = (a270 - 1);
		} else {

		}
	}
}
void calculate_outputm174(int input) {
	if (((((241 < a54) && (402 >= a54)) && (a196 == 12 && (a134 == 1 && (((input == inputs[3] && cf == 1) && a75 == 35) && (3 == a353[2]))))) && ((a324 == a232[0] && (a368 == 1 && (a256 == 33 && a307 == a227[0]))) && a383 == a226[0]))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a174 += (a174 + 20) > a174 ? 2 : 0;
		a133 += (a133 + 20) > a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a295 = a366[(a237 + 1)];
		a134 = 0;
		a184 = a157[((a196 + a196) - 21)];
	}
	if ((((((37 == a392[3]) && a134 == 1) && a382 <= -65) && a300 == 1) && ((a361 == 33 && (a249 <= 152 && (((a196 == 12 && (input == inputs[0] && cf == 1)) && ((241 < a54) && (402 >= a54))) && a75 == 35))) && a361 == 33))) {
		a164 += (a164 + 20) > a164 ? 2 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		a75 = 33;
		a132 = 0;
		a77 = (a359 + 7);
		a1 = a87[(a77 + -7)];
	}
	if (((a225 == a205[0] && ((241 < a54) && (402 >= a54))) && (((a312 == 33 && (a206 == 4 && ((a75 == 35 && (((cf == 1 && a134 == 1) && a196 == 12) && a333 <= -47)) && input == inputs[7]))) && a310 <= 160) && a302 == a346[0]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		a94 += (a94 + 20) > a94 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a132 = 0;
		a75 = 33;
		a77 = (a320 - -4);
		a1 = a87[((a359 - a270) - -9)];
	}
	if ((((a224 == 33 && (a243 <= -179 && ((a75 == 35 && (cf == 1 && ((241 < a54) && (402 >= a54)))) && a196 == 12))) && input == inputs[6]) && (a134 == 1 && (a277 <= -10 && (a234 == a372[0] && (a218 == 33 && (3 == a353[2]))))))) {
		a164 += (a164 + 20) > a164 ? 2 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		a75 = 34;
		a57 = a196;
		a81 = a167[(a338 - 3)];
		a99 = a26[(a57 + -10)];
	}
	if (((((241 < a54) && (402 >= a54)) && (a75 == 35 && ((24 == a370[2]) && ((24 == a370[2]) && (((45 == a228[1]) && a201 <= -199) && a206 == 4))))) && (a196 == 12 && (((cf == 1 && a134 == 1) && input == inputs[5]) && a312 == 33)))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a35 -= (a35 - 20) < a35 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a395 = 0;
	}
	if (((a243 <= -179 && (a260 == 1 && ((a75 == 35 && (a134 == 1 && (((241 < a54) && (402 >= a54)) && cf == 1))) && a378 == 1))) && (((3 == a353[2]) && ((a361 == 33 && input == inputs[4]) && a196 == 12)) && (47 == a265[5])))) {
		a164 += (a164 + 20) > a164 ? 2 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a107 = 34;
		a173 = 34;
		a75 = 32;
		a172 = ((a206 * a270) - 32);
	}
	if (((a196 == 12 && (a134 == 1 && (((241 < a54) && (402 >= a54)) && cf == 1))) && (a357 <= -188 && (((3 == a353[2]) && (a75 == 35 && (a361 == 33 && (input == inputs[8] && (a320 == 6 && (37 == a392[3])))))) && a225 == a205[0])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if (((a184 == 8 && a224 == 34) || !(a141 == 9))) {
			a57 = (a206 + 12);
			a183 = 36;
			a75 = 34;
			a278 = a326[(a196 - 7)];
		} else {
			a277 = ((((((a277 % 78) + 146) * 9) / 10) - 29080) - -29015);
			a296 = a384;
			a323 = a398;
			a320 = 10;
			a307 = a227[7];
			a224 = 32;
			a239 = a299;
			a386 = (((27 / -5) / 5) + -9584);
			a137 = a117;
			a206 = 11;
			a235 = a216[7];
			a392 = a208;
			a358 = a348;
			a202 = a217[7];
			a300 = 0;
			a234 = a372[0];
			a357 = (((((a357 * -2) / 10) * 10) / 9) * 4);
			a228 = a264;
			a302 = a346[0];
			a339 = 1;
			a225 = a205[4];
			a237 = 10;
			a383 = a226[6];
			a313 = 36;
			a312 = 33;
			a211 = 4;
			a243 = (((((a243 - 0) % 43) - 98) * 9) / 10);
			a373 = 0;
			a276 = a289;
			a353 = a241;
			a201 = ((((a201 / 5) % 94) - -130) - 10);
			a270 = 10;
			a249 = ((((a249 % 14750) - -15249) * 1) + 1);
			a338 = 7;
			a378 = 0;
			a382 = ((((a382 * 1) + 18776) / 5) - -10007);
			a368 = 0;
			a57 = ((a230 - a230) + 13);
			a260 = 0;
			a398 = 16;
			a329 = 33;
			a333 = ((((a333 % 14976) + -47) + -4925) - 7438);
			a359 = 8;
			a324 = a232[5];
			a310 = ((((a310 - 0) % 15080) - 14919) - 1);
			a395 = 0;
			a336 = 0;
			a269 = 34;
			a240 = 0;
			a370 = a318;
			a75 = 34;
			a207 = 35;
			a218 = 32;
			a256 = 35;
			a361 = 32;
			a265 = a376;
			a230 = 4;
		}
	}
	if (((input == inputs[2] && ((a302 == a346[0] && (a234 == a372[0] && ((24 == a370[2]) && (a75 == 35 && ((a134 == 1 && cf == 1) && ((241 < a54) && (402 >= a54))))))) && (81 == a296[3]))) && ((a196 == 12 && a338 == 3) && (24 == a370[2])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a172 = (a196 - 5);
		a75 = 32;
		a173 = 34;
		a99 = a26[(a320 + -6)];
	}
	if ((((a134 == 1 && ((cf == 1 && ((241 < a54) && (402 >= a54))) && input == inputs[9])) && a312 == 33) && ((a218 == 33 && (a211 == 1 && (((a196 == 12 && a243 <= -179) && a373 == 1) && a211 == 1))) && a75 == 35))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if ((a339 == 1 || a123 != 1)) {
			a300 = 0;
			a235 = a216[5];
			a265 = a376;
			a361 = 32;
			a207 = 35;
			a373 = 0;
			a324 = a232[6];
			a256 = 36;
			a211 = 6;
			a249 = (((((a249 + 26431) - 9895) * 1) % 14750) - -15249);
			a296 = a384;
			a353 = a399;
			a260 = 0;
			a357 = (((a357 - -9410) + -7092) + 27855);
			a240 = 0;
			a370 = a311;
			a134 = 0;
			a310 = (((((a310 % 77) - -237) * 1) - 19646) + 19648);
			a307 = a227[4];
			a395 = 0;
			a210 = 1;
			a234 = a372[2];
			a237 = 10;
			a392 = a257;
			a378 = 0;
			a295 = a366[(a398 - 3)];
		} else {
			a75 = 33;
			a132 = 0;
			a129 = a92[(a230 - -2)];
			a77 = ((a196 + a196) + -12);
		}
	}
	if ((((a75 == 35 && (input == inputs[1] && (a339 == 1 && a234 == a372[0]))) && (81 == a296[3])) && ((((67 == a358[2]) && (((241 < a54) && (402 >= a54)) && (a134 == 1 && (a196 == 12 && cf == 1)))) && a237 == 3) && a312 == 33))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 -= (a12 - 20) < a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a178 += (a178 + 20) > a178 ? 4 : 0;
		cf = 0;
		a329 = 35;
		a286 = a294[2];
		a398 = 15;
		a234 = a372[6];
		a300 = 1;
		a44 = 34;
		a75 = 33;
		a132 = 0;
		a77 = (a206 + 4);
	}
}
void calculate_outputm175(int input) {
	if (((a249 <= 152 && (a243 <= -179 && (((a135 == 33 && (input == inputs[8] && (a75 == 35 && (a196 == 15 && cf == 1)))) && a206 == 4) && a134 == 1))) && (a300 == 1 && (a307 == a227[0] && (47 == a265[5]))))) {
		a120 += (a120 + 20) > a120 ? 1 : 0;
		cf = 0;
		a211 = (a398 - 9);
		a265 = a376;
		a143 = 34;
		a300 = 1;
		a230 = (a196 + -10);
		a270 = (a359 + 9);
		a378 = 1;
		a260 = 1;
		a307 = a227[(a206 - 2)];
		a329 = 32;
		a398 = a270;
		a373 = 0;
		a320 = ((a338 / a230) - -8);
		a312 = 33;
		a368 = 1;
		a75 = 34;
		a240 = 1;
		a296 = a212;
		a382 = ((((((((a382 * a249) % 14999) - 9691) % 107) - -69) * 5) % 107) + 69);
		a218 = 34;
		a57 = (a196 + -4);
		a173 = 33;
		a361 = 34;
		a324 = a232[(a237 + -1)];
		a201 = (((((((a333 * a333) % 14999) % 94) - 1) * 5) % 94) + 82);
		a234 = a372[(a320 + -6)];
		a333 = (((((((a333 * a357) % 14999) + 13757) % 14) - -163) + -16092) - -16092);
	}
	if ((((a218 == 33 && (a373 == 1 && a134 == 1)) && a378 == 1) && ((a382 <= -65 && (a286 == a294[0] && (a75 == 35 && (input == inputs[4] && (a135 == 33 && (cf == 1 && a196 == 15)))))) && a234 == a372[0]))) {
		a122 -= (a122 - 20) < a122 ? 3 : 0;
		cf = 0;
		a339 = 0;
		a324 = a232[((a211 - a398) + 9)];
		a57 = (a398 + 3);
		a382 = (((((((a382 * a243) % 14999) / 5) - 17944) - -2791) % 107) + 121);
		a307 = a227[(a57 + -11)];
		a300 = 1;
		a154 = (a359 - -12);
		a218 = 34;
		a338 = (a320 + -1);
		a398 = (a196 - 4);
		a239 = a268;
		a228 = a292;
		a137 = a189;
		a240 = 1;
		a333 = (((((((a333 * a357) % 14999) * 2) * 1) + 1) % 14) + 163);
		a276 = a250;
		a75 = 34;
		a359 = ((a211 * a237) - 4);
	}
}
void calculate_outputm176(int input) {
	if (((a382 <= -65 && (a300 == 1 && (a134 == 1 && (a382 <= -65 && (a196 == 15 && ((36 == a239[5]) && a211 == 1)))))) && (a361 == 33 && (a75 == 35 && ((cf == 1 && input == inputs[8]) && a135 == 32))))) {
		cf = 0;
		a224 = 32;
		a201 = (((((((a382 * a249) % 14999) % 94) - -82) - 20151) / 5) - -4133);
		a173 = 33;
		a240 = 1;
		a234 = a372[(a338 + -1)];
		a277 = ((((((a277 * a201) % 14999) % 78) + 68) + 0) + 0);
		a373 = 0;
		a358 = a335;
		a320 = ((a270 * a196) - 142);
		a143 = 34;
		a368 = 1;
		a329 = 32;
		a398 = (a270 + 2);
		a395 = 0;
		a57 = ((a196 - a196) + 11);
		a312 = 33;
		a75 = 34;
		a230 = (a359 + 2);
		a207 = 32;
		a333 = ((((((a333 * a357) % 14999) % 14) - -162) + -1) + 0);
		a296 = a212;
		a265 = a376;
		a300 = 1;
		a382 = ((((((a382 * a357) % 14999) % 107) - -69) + 1) - 2);
		a361 = 34;
		a260 = 1;
		a270 = ((a398 * a320) - 84);
	}
	if (((((a277 <= -10 && input == inputs[4]) && a395 == 1) && a300 == 1) && (((((a134 == 1 && ((a196 == 15 && cf == 1) && a75 == 35)) && a135 == 32) && a207 == 33) && a277 <= -10) && a224 == 33))) {
		cf = 0;
		a239 = a268;
		a270 = (a359 - -8);
		a240 = 1;
		a338 = (a196 - 10);
		a75 = 34;
		a137 = a189;
		a207 = 32;
		a395 = 0;
		a300 = 1;
		a228 = a292;
		a382 = ((((((a382 * a357) % 14999) / 5) % 107) + 68) + 0);
		a359 = ((a237 / a211) - -2);
		a211 = (a320 + -3);
		a276 = a250;
		a339 = 0;
		a333 = ((((((a333 * a277) % 14999) % 14) - -148) + 14) - 5);
		a57 = (a320 - -7);
		a224 = 32;
		a154 = ((a320 + a57) + -4);
		a277 = ((((((a277 * a386) % 14999) % 78) + 68) + 0) - 0);
	}
}
void calculate_outputm177(int input) {
	if (((((a237 == 3 && a313 == 33) && (81 == a296[3])) && a368 == 1) && (((a134 == 1 && ((a75 == 35 && (input == inputs[5] && (cf == 1 && a196 == 15))) && a135 == 34)) && a211 == 1) && a235 == a216[0]))) {
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		cf = 0;
		a312 = 32;
		a228 = a264;
		a373 = 0;
		a256 = 32;
		a239 = a242;
		a235 = a216[(a211 + a211)];
		a128 = (a196 - 3);
		a339 = 0;
		a368 = 0;
		a300 = 1;
		a386 = (((((a382 * a382) % 14999) - -12706) + 140) - 33135);
		a361 = 32;
		a286 = a294[((a211 - a206) + 4)];
		a75 = 32;
		a333 = ((((((a333 * a310) % 14999) % 96) - -49) + 0) - 0);
		a237 = ((a320 / a338) + 2);
		a276 = a250;
		a243 = (((((((a357 * a357) % 14999) + -23615) * 1) * 1) % 43) - 78);
		a240 = 0;
		a269 = 34;
		a206 = (a320 - a211);
		a336 = 0;
		a313 = 32;
		a249 = ((((((a249 * a277) % 14999) % 101) + 254) - 1) - -1);
		a265 = a293;
		a359 = a230;
		a383 = a226[a211];
		a382 = ((((((a382 * a201) % 14999) % 107) + -7) - 27) - -55);
		a296 = a362;
		a358 = a348;
		a202 = a217[(a270 - 11)];
		a225 = a205[(a206 + -4)];
		a302 = a346[(a398 - 10)];
		a141 = a47[(a128 + -6)];
		a338 = (a128 + -8);
		a378 = 1;
		a234 = a372[(a206 + -4)];
		a320 = ((a196 - a211) + -6);
		a218 = 32;
		a173 = 36;
		a211 = (a196 + -12);
	}
}
void calculate_outputm178(int input) {
	if (((a237 == 3 && (((24 == a370[2]) && a134 == 1) && (37 == a392[3]))) && (a75 == 35 && ((a386 <= 77 && (a312 == 33 && (a382 <= -65 && ((cf == 1 && a196 == 17) && input == inputs[8])))) && a91 == 13)))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a94 += (a94 + 20) > a94 ? 2 : 0;
		cf = 0;
		a81 = a167[(a398 - 5)];
		a278 = a326[(a196 - a398)];
		a75 = 34;
		a57 = ((a196 + a91) - 14);
	}
	if ((((((a207 == 33 && (a243 <= -179 && (3 == a353[2]))) && a91 == 13) && input == inputs[5]) && a277 <= -10) && (a75 == 35 && (a269 == 33 && (((a134 == 1 && cf == 1) && a196 == 17) && a383 == a226[0]))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		a94 -= (a94 - 20) < a94 ? 1 : 0;
		cf = 0;
		if (((a300 == 1 && (38 == a370[4])) && !(a1 == 5))) {
			a269 = 35;
			a358 = a348;
			a307 = a227[6];
			a382 = ((((a382 % 12) - 40) - 17653) + 17649);
			a57 = ((a359 - a320) - -20);
			a277 = ((((a277 / 5) / 5) - 7289) + 12842);
			a276 = a289;
			a40 = a83;
			a336 = 0;
			a353 = a263;
			a320 = 6;
			a265 = a293;
			a240 = 0;
			a386 = ((((a386 % 15038) - 14960) - 2) + 0);
			a333 = ((((a333 % 96) - -49) * 5) / 5);
			a75 = 34;
			a378 = 0;
			a211 = 2;
			a239 = a242;
			a25 = a76;
		} else {
			a75 = 32;
			a81 = a167[((a338 * a359) + -2)];
			a383 = a226[3];
			a173 = 32;
			a270 = 15;
			a269 = 35;
			a324 = a232[4];
			a125 = a30[(a206 - -1)];
			a277 = ((((a277 / 5) + -5703) * 10) / -9);
			a336 = 1;
			a353 = a399;
			a395 = 1;
			a300 = 1;
			a207 = 36;
			a228 = a292;
			a320 = 6;
			a240 = 1;
			a230 = 7;
			a243 = ((((((a243 % 14910) + -179) / 5) - -21439) * -1) / 10);
			a296 = a362;
			a249 = (((19 + -28726) / 5) / 5);
			a260 = 1;
			a373 = 1;
			a256 = 34;
			a312 = 35;
			a386 = ((((a386 % 15038) - 14960) - 2) * 1);
			a206 = 8;
			a276 = a250;
			a237 = 5;
			a382 = ((((a382 % 14967) + -65) * 1) - 6574);
			a265 = a376;
			a392 = a208;
			a239 = a268;
			a333 = (((((a333 % 14976) - 47) + 29003) + 284) - 41776);
			a218 = 36;
			a357 = ((((28 + 237) + -23178) * 10) / -9);
			a378 = 1;
			a338 = 6;
			a339 = 1;
			a329 = 36;
			a202 = a217[6];
			a398 = 17;
			a302 = a346[2];
			a211 = 6;
			a368 = 1;
			a370 = a318;
			a307 = a227[5];
			a359 = 7;
		}
	}
	if (((((input == inputs[3] && a324 == a232[0]) && a361 == 33) && a329 == 33) && (a333 <= -47 && ((a134 == 1 && (a196 == 17 && ((a75 == 35 && (a91 == 13 && cf == 1)) && a260 == 1))) && a383 == a226[0])))) {
		a122 -= (a122 - 20) < a122 ? 2 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a35 += (a35 + 20) > a35 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		a324 = a232[6];
		a276 = a289;
		a240 = 0;
		a359 = 10;
		a339 = 1;
		a353 = a241;
		a386 = ((((a386 - -14105) / 5) / 5) - 4683);
		a75 = 34;
		a296 = a212;
		a211 = 6;
		a225 = a205[3];
		a313 = 35;
		a300 = 1;
		a336 = 0;
		a206 = 11;
		a378 = 1;
		a370 = a318;
		a368 = 0;
		a320 = 10;
		a333 = ((((((a333 % 96) + 109) * 9) / 10) - 10764) + 10740);
		a235 = a216[0];
		a207 = 35;
		a260 = 0;
		a265 = a293;
		a398 = 15;
		a237 = 9;
		a239 = a242;
		a338 = 4;
		a256 = 33;
		a307 = a227[6];
		a57 = (a196 + -4);
		a243 = (((((a243 - 0) % 43) + -93) + -15994) - -16001);
		a277 = (((((a277 * 1) % 78) + 125) * 9) / 10);
		a234 = a372[3];
		a312 = 36;
		a154 = ((a91 / a57) + 15);
		a358 = a348;
		a230 = 3;
		a392 = a257;
		a395 = 0;
		a329 = 35;
		a269 = 35;
		a373 = 1;
		a270 = 16;
		a286 = a294[0];
		a224 = 33;
		a361 = 33;
		a228 = a229;
		a383 = a226[7];
		a382 = (((((a382 % 14967) + -65) / 5) * 10) / 2);
		a137 = a189;
	}
	if (((a196 == 17 && (((a134 == 1 && (a91 == 13 && cf == 1)) && input == inputs[7]) && a75 == 35)) && (((37 == a392[3]) && (a336 == 1 && ((81 == a296[3]) && (a300 == 1 && a260 == 1)))) && a324 == a232[0]))) {
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a174 += (a174 + 20) > a174 ? 4 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		cf = 0;
		if (a102 == a127[1]) {
			a382 = ((((a382 % 12) + -49) + -23605) + 23609);
			a336 = 0;
			a265 = a293;
			a75 = 34;
			a307 = a227[5];
			a276 = a289;
			a386 = (((((a386 % 14837) + 15162) / 5) * 5) - -5);
			a333 = ((((a333 - 0) % 14976) + -47) - 351);
			a277 = (((((a277 * 1) % 14995) - 10) * 10) / 9);
			a40 = a83;
			a57 = ((a91 - a320) - -10);
			a240 = 0;
			a269 = 35;
			a378 = 0;
			a353 = a241;
			a239 = a299;
			a358 = a351;
			a211 = 2;
			a320 = 13;
			a25 = a76;
		} else {
			a210 = 1;
			a173 = 32;
			a75 = 32;
			a125 = a30[(a91 + -11)];
		}
	}
	if ((((((a91 == 13 && (a75 == 35 && (a196 == 17 && cf == 1))) && a324 == a232[0]) && a134 == 1) && a324 == a232[0]) && ((input == inputs[2] && (a256 == 33 && (a339 == 1 && a300 == 1))) && a307 == a227[0]))) {
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a98 += (a98 + 20) > a98 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 2 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		a202 = a217[7];
		a64 = 0;
		a302 = a346[5];
		a146 = 0;
		a218 = 34;
		a75 = 36;
		a357 = (((((39 * 10) / -6) + 19389) + 6991) - 26383);
		a73 = (((18 - -495) * 5) + 17841);
	}
	if ((((a224 == 33 && (((a378 == 1 && (47 == a265[5])) && a91 == 13) && a270 == 10)) && a270 == 10) && ((a368 == 1 && (((cf == 1 && a134 == 1) && a75 == 35) && a196 == 17)) && input == inputs[1]))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a89 -= (a89 - 20) < a89 ? 2 : 0;
		a169 -= (a169 - 20) < a169 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		cf = 0;
		if (a77 == 10) {
			a313 = 32;
			a202 = a217[7];
			a146 = 1;
			a218 = 32;
			a333 = (((a333 * 1) / 5) + 28704);
			a296 = a212;
			a361 = 33;
			a310 = ((((19 + 22603) / 5) * 10) / 9);
			a383 = a226[0];
			a235 = a216[3];
			a249 = ((((95 - -119) * 5) - -21327) + -22179);
			a286 = a294[5];
			a378 = 1;
			a357 = ((((((36 * 10) / 18) * 10) / -9) * 5) + 122);
			a46 = a18;
			a358 = a348;
			a302 = a346[4];
			a75 = 36;
			a201 = (((76 + 6943) * 4) * 1);
			a13 = (((((36 * 9) / 10) * 10) / 9) * 5);
		} else {
			a307 = a227[1];
			a368 = 0;
			a329 = 32;
			a357 = (((76 - 28812) + 28750) - 68);
			a207 = 34;
			a239 = a268;
			a300 = 0;
			a359 = 3;
			a383 = a226[4];
			a206 = 7;
			a228 = a229;
			a382 = (((((a382 + 0) % 14911) + 15087) - 15787) - -22318);
			a320 = 8;
			a125 = a30[(a91 + -12)];
			a296 = a212;
			a270 = 13;
			a260 = 1;
			a234 = a372[5];
			a398 = 16;
			a269 = 33;
			a240 = 1;
			a358 = a348;
			a202 = a217[2];
			a277 = ((((((a277 / 5) % 95) + 275) / 5) * 49) / 10);
			a336 = 0;
			a265 = a376;
			a392 = a304;
			a75 = 32;
			a256 = 35;
			a211 = 3;
			a173 = 32;
			a338 = 5;
			a378 = 0;
			a361 = 32;
			a386 = (((((a386 % 14837) - -15162) * 1) / 5) - -8851);
			a395 = 1;
			a353 = a263;
			a224 = 33;
			a370 = a311;
			a243 = (((((a243 + 25914) % 14910) + -15088) + 24884) - 24885);
			a249 = ((((75 + 7730) + -7472) - -4437) + -4440);
			a230 = 8;
			a324 = a232[7];
			a373 = 0;
			a235 = a216[1];
			a339 = 1;
			a302 = a346[7];
			a312 = 33;
			a237 = 7;
			a276 = a250;
			a218 = 36;
			a333 = ((((a333 % 14976) + -47) - 13392) - 1095);
			a8 = (a196 - 6);
		}
	}
	if (((a91 == 13 && ((cf == 1 && a196 == 17) && a134 == 1)) && ((81 == a296[3]) && (a230 == 3 && ((a75 == 35 && (input == inputs[0] && (a307 == a227[0] && ((36 == a239[5]) && a398 == 10)))) && a307 == a227[0]))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		cf = 0;
		a143 = 32;
		a75 = 34;
		a14 = a79[((a91 / a270) + 3)];
		a57 = ((a196 / a91) - -10);
	}
	if (((a196 == 17 && (((a300 == 1 && (((98 == a276[2]) && a75 == 35) && a230 == 3)) && a234 == a372[0]) && a224 == 33)) && (a312 == 33 && ((a91 == 13 && (cf == 1 && input == inputs[6])) && a134 == 1)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 2 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		cf = 0;
		a300 = 0;
		a276 = a250;
		a358 = a348;
		a237 = 5;
		a75 = 32;
		a386 = (((((a386 * 1) % 14837) - -15162) + -24827) + 24829);
		a265 = a376;
		a269 = 35;
		a235 = a216[3];
		a368 = 0;
		a329 = 36;
		a256 = 36;
		a361 = 35;
		a218 = 33;
		a338 = 9;
		a173 = 32;
		a392 = a304;
		a230 = 10;
		a395 = 1;
		a353 = a399;
		a202 = a217[2];
		a234 = a372[5];
		a224 = 34;
		a125 = a30[((a196 + a196) - 33)];
		a373 = 0;
		a239 = a268;
		a243 = (((((a243 % 14910) + -179) * 10) / 9) + -5392);
		a307 = a227[1];
		a320 = 9;
		a240 = 1;
		a277 = ((((a277 % 14830) - -15169) - 11521) + 12405);
		a357 = (((21 - -19249) + 7832) - -316);
		a324 = a232[6];
		a302 = a346[5];
		a206 = 11;
		a398 = 17;
		a378 = 0;
		a249 = ((((51 / 5) - -6594) / 5) + -1093);
		a359 = 8;
		a383 = a226[5];
		a260 = 1;
		a339 = 1;
		a207 = 36;
		a312 = 36;
		a370 = a318;
		a382 = ((((a382 % 14967) - 65) - 8294) / 5);
		a228 = a292;
		a211 = 7;
		a333 = ((((a333 % 14976) + -47) + -10585) * 1);
		a336 = 0;
		a270 = 17;
		a296 = a212;
		a8 = ((a196 - a196) + 11);
	}
	if (((((cf == 1 && a75 == 35) && input == inputs[4]) && a230 == 3) && (a206 == 4 && ((67 == a358[2]) && (((a134 == 1 && ((a320 == 6 && a307 == a227[0]) && a196 == 17)) && a91 == 13) && a270 == 10))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 3 : 0;
		a94 -= (a94 - 20) < a94 ? 1 : 0;
		cf = 0;
		a57 = (a359 + 12);
		a72 = (((98 * 5) + -20794) - -35334);
		a75 = 34;
		a17 = (((((a72 * a72) % 14999) - 24989) * 1) + -3618);
	}
	if (((((a206 == 4 && (((((input == inputs[9] && cf == 1) && a196 == 17) && a75 == 35) && a134 == 1) && a333 <= -47)) && a91 == 13) && a211 == 1) && ((a336 == 1 && a368 == 1) && a386 <= 77))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a133 += (a133 + 20) > a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		a31 += (a31 + 20) > a31 ? 3 : 0;
		cf = 0;
		a75 = 36;
		a286 = a294[1];
		a202 = a217[5];
		a358 = a348;
		a146 = 1;
		a296 = a362;
		a218 = 36;
		a201 = ((((92 * 5) / 5) * 10) / 5);
		a46 = a18;
		a310 = (((((40 * 10) / 1) - -8488) + -19772) + 36368);
		a333 = ((((a333 % 14976) + -47) + -366) + -1549);
		a302 = a346[4];
		a357 = ((((81 * 5) * 5) / 5) + -488);
		a249 = (((((3 * 1639) / 10) * 5) + 2264) - 4247);
		a383 = a226[0];
		a378 = 1;
		a361 = 35;
		a235 = a216[3];
		a313 = 32;
		a13 = (((39 + -26) - 22) / 5);
	}
}
void calculate_outputm16(int input) {
	if ((((((3 == a353[2]) && a230 == 3) && a386 <= 77) && a398 == 10) && (a373 == 1 && (a206 == 4 && (cf == 1 && a196 == 10))))) {
		if ((((a277 <= -10 && ((a129 == a92[2] && cf == 1) && a225 == a205[0])) && a368 == 1) && (a312 == 33 && (a269 == 33 && a260 == 1)))) {
			calculate_outputm171(input);
		}
	}
	if ((((((67 == a358[2]) && ((cf == 1 && a196 == 12) && a324 == a232[0])) && (47 == a265[5])) && a338 == 3) && (a243 <= -179 && a211 == 1))) {
		if (((a300 == 1 && (a256 == 33 && a359 == 3)) && (a237 == 3 && (a235 == a216[0] && ((((241 < a54) && (402 >= a54)) && cf == 1) && a310 <= 160))))) {
			calculate_outputm174(input);
		}
	}
	if (((a249 <= 152 && (a359 == 3 && a382 <= -65)) && (((a225 == a205[0] && (a196 == 15 && cf == 1)) && a361 == 33) && (47 == a265[5])))) {
		if (((((36 == a239[5]) && ((a324 == a232[0] && a361 == 33) && a307 == a227[0])) && a243 <= -179) && (a225 == a205[0] && (cf == 1 && a135 == 33)))) {
			calculate_outputm175(input);
		}
		if (((a270 == 10 && (a135 == 32 && cf == 1)) && (((((67 == a358[2]) && a300 == 1) && a211 == 1) && a333 <= -47) && a224 == 33))) {
			calculate_outputm176(input);
		}
		if (((a206 == 4 && ((a218 == 33 && a256 == 33) && a234 == a372[0])) && ((a312 == 33 && (cf == 1 && a135 == 34)) && a339 == 1))) {
			calculate_outputm177(input);
		}
	}
	if (((((a207 == 33 && (a270 == 10 && (cf == 1 && a196 == 17))) && (47 == a265[5])) && a338 == 3) && (a269 == 33 && a230 == 3))) {
		if ((((a277 <= -10 && (36 == a239[5])) && a361 == 33) && ((81 == a296[3]) && (((a91 == 13 && cf == 1) && a269 == 33) && a307 == a227[0])))) {
			calculate_outputm178(input);
		}
	}
}
void calculate_outputm181(int input) {
	if ((((3 == a353[2]) && (a338 == 3 && ((a134 != 1 && a378 == 1) && a225 == a205[0]))) && ((((((a75 == 35 && cf == 1) && a295 == a366[0]) && input == inputs[8]) && a338 == 3) && a196 == 16) && (37 == a392[3])))) {
		a178 += (a178 + 20) > a178 ? 3 : 0;
		cf = 0;
		a378 = 1;
		a75 = 34;
		a57 = (a196 + -1);
		a211 = (a196 + -13);
		a72 = (((29 - 4377) * 5) / 5);
		a265 = a376;
		a218 = 34;
		a141 = a47[((a320 - a57) + 12)];
		a336 = 1;
		a320 = (a237 + 3);
		a353 = a399;
		a392 = a304;
		a338 = (a57 + -10);
		a269 = 34;
		a228 = a292;
		a276 = a250;
		a333 = ((((((((a333 * a201) % 14999) % 14) + 159) * 5) + 19183) % 14) + 151);
		a201 = ((((((a201 * a357) % 14999) + -2451) - -7938) % 94) + 83);
	}
}
void calculate_outputm182(int input) {
	if (((a196 == 17 && (((a75 == 35 && (cf == 1 && input == inputs[4])) && a368 == 1) && a207 == 33)) && (a134 != 1 && (((a295 == a366[0] && (a234 == a372[0] && a361 == 33)) && a395 == 1) && (37 == a392[3]))))) {
		a168 += (a168 + 20) > a168 ? 2 : 0;
		cf = 0;
		a225 = a205[(a398 - 10)];
		a57 = ((a320 + a359) + 4);
		a154 = (a230 + 8);
		a310 = (((((((a310 * a357) % 14999) % 20) - -336) * 5) % 20) + 320);
		a202 = a217[(a237 + -3)];
		a339 = 0;
		a269 = 34;
		a395 = 0;
		a302 = a346[(a320 - 4)];
		a368 = 1;
		a218 = 34;
		a228 = a292;
		a276 = a250;
		a353 = a399;
		a224 = 32;
		a333 = (((((((a333 * a201) % 14999) % 14) + 150) / 5) - -15003) - 14871);
		a359 = a237;
		a201 = (((((((a382 * a277) % 14999) % 93) + -104) / 5) * 5) + -2);
		a358 = a335;
		a392 = a304;
		a207 = 32;
		a382 = (((((a357 * a357) / 5) - -3728) % 107) - -28);
		a338 = a237;
		a312 = 34;
		a75 = 34;
		a329 = 34;
		a336 = 1;
		a137 = a189;
		a320 = (a154 - 3);
	}
	if (((((input == inputs[2] && a382 <= -65) && a310 <= 160) && a224 == 33) && (((a302 == a346[0] && (a134 != 1 && (a196 == 17 && (a295 == a366[0] && (cf == 1 && a75 == 35))))) && a225 == a205[0]) && a320 == 6))) {
		a178 += (a178 + 20) > a178 ? 4 : 0;
		cf = 0;
		a324 = a232[((a230 / a206) + 1)];
		a296 = a362;
		a373 = 0;
		a357 = ((((57 * -31) / 10) / 5) + -105);
		a338 = ((a230 * a230) + -5);
		a239 = a242;
		a329 = 32;
		a382 = ((((((a382 * a333) % 14999) % 12) - 54) + -1) + 1);
		a207 = 32;
		a201 = (((((((a201 * a310) % 14999) * 2) % 93) + -104) / 5) + -22);
		a237 = ((a230 + a338) + -2);
		a312 = 34;
		a383 = a226[((a206 * a320) + -29)];
		a398 = a270;
		a370 = a285;
		a395 = 0;
		a225 = a205[(a270 + -10)];
		a361 = 32;
		a224 = 32;
		a218 = 32;
		a173 = 32;
		a211 = (a270 - 9);
		a368 = 0;
		a310 = (((((((a357 * a201) % 14999) % 77) - -209) * 5) % 77) - -233);
		a260 = 1;
		a359 = (a398 - 7);
		a300 = 0;
		a210 = 0;
		a302 = a346[(a398 + -9)];
		a277 = (((86 - 3502) + -9019) + -15718);
		a75 = 32;
		a336 = 0;
		a307 = a227[(a338 + -4)];
		a320 = (a196 - 10);
		a339 = 0;
		a234 = a372[(a338 + -3)];
		a243 = ((((((a357 * a382) / 5) * 5) - 22779) % 43) + -68);
		a125 = a30[(a230 - -1)];
		a240 = 0;
		a202 = a217[(a230 + -2)];
		a256 = 34;
		a333 = ((((((a382 * a357) % 14) + 158) * 5) % 14) + 155);
		a265 = a293;
		a392 = a257;
		a276 = a289;
		a286 = a294[((a206 / a270) + 1)];
		a235 = a216[((a359 - a359) - -2)];
		a230 = (a206 - 1);
	}
}
void calculate_outputm183(int input) {
	if (((a171 == 32 && ((a295 == a366[2] && ((a302 == a346[0] && (((a75 == 35 && cf == 1) && input == inputs[8]) && (67 == a358[2]))) && (37 == a392[3]))) && a134 != 1)) && (((36 == a239[5]) && a312 == 33) && a235 == a216[0]))) {
		a51 += (a51 + 20) > a51 ? 1 : 0;
		cf = 0;
		a207 = 34;
		a324 = a232[((a237 + a359) + -6)];
		a72 = (((89 + 9037) + -30697) + -4469);
		a276 = a250;
		a218 = 34;
		a269 = 34;
		a141 = a47[((a320 + a270) - 13)];
		a235 = a216[(a270 + -8)];
		a265 = a376;
		a336 = 1;
		a353 = a399;
		a75 = 34;
		a57 = 15;
		a228 = a292;
		a392 = a304;
		a302 = a346[(a359 + -1)];
		a320 = ((a206 + a338) + -3);
		a333 = (((((((a333 * a382) % 14999) + 1002) % 14) + 162) / 5) + 133);
		a201 = ((((((a201 * a386) % 14999) - -4267) * 1) % 94) - -83);
		a270 = ((a230 / a206) - -12);
	}
}
void calculate_outputm184(int input) {
	if ((((((input == inputs[6] && a324 == a232[0]) && a230 == 3) && a75 == 35) && a333 <= -47) && ((36 == a239[5]) && (((((cf == 1 && a134 != 1) && a295 == a366[2]) && a171 == 36) && a243 <= -179) && a206 == 4)))) {
		a174 += (a174 + 20) > a174 ? 1 : 0;
		cf = 0;
		a269 = 32;
		a75 = 32;
		a243 = (((((((a243 * a310) % 14999) / 5) % 11) + -167) + 10575) - 10574);
		a378 = 0;
		a276 = a289;
		a239 = a268;
		a324 = a232[((a320 * a237) - 17)];
		a173 = 32;
		a339 = 0;
		a320 = (a359 + 4);
		a353 = a241;
		a8 = (a338 - -7);
		a358 = a351;
		a224 = 32;
		a218 = 34;
		a125 = a30[(a237 - 2)];
		a237 = (a338 + 1);
		a228 = a264;
		a230 = (a338 + 1);
		a207 = 34;
		a206 = (a359 - -2);
		a359 = a230;
		a338 = (a270 - 7);
	}
}
void calculate_outputm189(int input) {
	if (((((a333 <= -47 && a134 != 1) && a260 == 1) && a201 <= -199) && (((((a295 == a366[4] && ((a75 == 35 && cf == 1) && input == inputs[9])) && a338 == 3) && a184 == a157[7]) && a383 == a226[0]) && a313 == 33))) {
		a31 += (a31 + 20) > a31 ? 2 : 0;
		cf = 0;
		a75 = 32;
		a338 = ((a230 * a270) + -40);
		a333 = (((((((a333 * a277) % 14999) * 2) - 0) * 1) % 14) - -161);
		a339 = 0;
		a206 = ((a230 * a320) + -19);
		a129 = a92[((a237 / a359) + 6)];
		a336 = 0;
		a383 = a226[((a206 - a338) - -1)];
		a228 = a292;
		a368 = 1;
		a218 = 34;
		a359 = a338;
		a260 = 0;
		a125 = a30[(a398 + -3)];
		a312 = 32;
		a240 = 0;
		a202 = a217[(a398 - 8)];
		a358 = a335;
		a224 = 32;
		a310 = ((((((a310 * a382) % 14999) - -440) / 5) % 77) + 239);
		a313 = 32;
		a276 = a289;
		a357 = ((((((((a357 * a201) % 14999) / 5) % 65) - 168) * 5) % 65) + -70);
		a269 = 34;
		a302 = a346[(a270 - 9)];
		a296 = a362;
		a370 = a285;
		a320 = (a338 - -3);
		a201 = ((((((a201 * a277) % 14999) * 2) % 93) + -105) - 1);
		a173 = 32;
		a398 = (a237 + 9);
		a237 = ((a359 - a338) + 4);
	}
	if (((((a240 == 1 && (a295 == a366[4] && ((((a224 == 33 && a260 == 1) && (24 == a370[2])) && a357 <= -188) && a249 <= 152))) && a75 == 35) && a134 != 1) && (input == inputs[1] && (a184 == a157[7] && cf == 1)))) {
		a162 -= (a162 - 20) < a162 ? 1 : 0;
		cf = 0;
		a370 = a285;
		a224 = 32;
		a75 = 32;
		a218 = 32;
		a260 = 0;
		a312 = 32;
		a373 = 0;
		a338 = (a320 + -2);
		a173 = 34;
		a172 = ((a206 * a237) - 8);
		a310 = (((((((a310 * a333) % 14999) * 2) % 77) - -238) + 4483) + -4483);
		a313 = 32;
		a357 = ((((((a357 * a249) % 14999) * 2) % 65) - 121) - 1);
		a274 = a290;
		a240 = 0;
		a320 = (a270 + -4);
	}
}
void calculate_outputm193(int input) {
	if ((((a201 <= -199 && ((((((cf == 1 && input == inputs[9]) && a295 == a366[7]) && a75 == 35) && (36 == a239[5])) && a210 == 1) && a329 == 33)) && a225 == a205[0]) && (a201 <= -199 && (a230 == 3 && a134 != 1)))) {
		cf = 0;
		a77 = (a206 + 6);
		a75 = 33;
		a338 = ((a359 / a237) - -4);
		a132 = 0;
		a1 = a87[(a398 - 4)];
		a224 = 32;
		a339 = 0;
		a386 = ((((((a386 * a382) % 14999) % 61) + 264) + -529) + 527);
		a336 = 1;
		a382 = ((((((a382 * a277) % 14999) % 107) - 35) - 2) / 5);
		a312 = 34;
		a329 = 34;
		a398 = (a206 - -7);
		a368 = 1;
		a270 = (a77 + 1);
	}
}
void calculate_outputm17(int input) {
	if (((a201 <= -199 && ((((cf == 1 && a295 == a366[0]) && (3 == a353[2])) && a359 == 3) && a329 == 33)) && (a338 == 3 && (47 == a265[5])))) {
		if ((((a338 == 3 && ((cf == 1 && a196 == 16) && (47 == a265[5]))) && a312 == 33) && ((a211 == 1 && (36 == a239[5])) && a224 == 33))) {
			calculate_outputm181(input);
		}
		if (((a312 == 33 && (cf == 1 && a196 == 17)) && (a202 == a217[0] && ((24 == a370[2]) && (a373 == 1 && ((37 == a392[3]) && a338 == 3)))))) {
			calculate_outputm182(input);
		}
	}
	if ((((((45 == a228[1]) && (a359 == 3 && a339 == 1)) && a207 == 33) && (3 == a353[2])) && (a324 == a232[0] && (cf == 1 && a295 == a366[2])))) {
		if (((a302 == a346[0] && ((a359 == 3 && a201 <= -199) && (47 == a265[5]))) && ((a359 == 3 && (a171 == 32 && cf == 1)) && a386 <= 77))) {
			calculate_outputm183(input);
		}
		if (((a211 == 1 && a206 == 4) && (a324 == a232[0] && (a338 == 3 && (a237 == 3 && (a378 == 1 && (a171 == 36 && cf == 1))))))) {
			calculate_outputm184(input);
		}
	}
	if (((a310 <= 160 && ((((81 == a296[3]) && a373 == 1) && a202 == a217[0]) && a201 <= -199)) && (a218 == 33 && (a295 == a366[4] && cf == 1)))) {
		if (((a312 == 33 && (a201 <= -199 && (a269 == 33 && ((24 == a370[2]) && ((81 == a296[3]) && a224 == 33))))) && (a184 == a157[7] && cf == 1))) {
			calculate_outputm189(input);
		}
	}
	if (((a269 == 33 && ((cf == 1 && a295 == a366[7]) && a368 == 1)) && (((a277 <= -10 && a270 == 10) && a386 <= 77) && a382 <= -65))) {
		if ((((a312 == 33 && (a333 <= -47 && a338 == 3)) && a313 == 33) && (((cf == 1 && a210 == 1) && a338 == 3) && a230 == 3))) {
			calculate_outputm193(input);
		}
	}
}
void calculate_outputm195(int input) {
	if ((((a312 == 33 && a211 == 1) && (45 == a228[1])) && (((input == inputs[6] && (a237 == 3 && ((((27 == a46[0]) && (a151 == 1 && cf == 1)) && a218 == 33) && a146 == 1))) && a75 == 36) && a260 == 1))) {
		a31 += (a31 + 20) > a31 ? 1 : 0;
		cf = 0;
		if (a278 == a326[7]) {
			a173 = 36;
			a312 = 33;
			a333 = (((((((a333 * a310) % 14999) / 5) + 17186) - 6917) * -1) / 10);
			a239 = a242;
			a383 = a226[(a398 + -10)];
			a277 = ((((((a201 * a386) % 14999) - -17701) % 78) - 8) + 21);
			a353 = a263;
			a218 = 33;
			a234 = a372[((a237 + a211) + -4)];
			a324 = a232[a211];
			a141 = a47[(a230 - 2)];
			a230 = (a211 + 2);
			a310 = (((((((a310 * a277) % 14999) * 2) % 77) + 237) + -16437) - -16439);
			a398 = ((a338 * a211) - -7);
			a300 = 1;
			a313 = 32;
			a237 = a338;
			a42 = (a359 - -5);
			a260 = 0;
			a75 = 32;
			a270 = ((a211 - a320) - -17);
			a307 = a227[(a359 + -2)];
			a225 = a205[((a211 - a206) + 4)];
			a228 = a229;
			a359 = ((a338 * a338) + -6);
			a373 = 1;
			a338 = ((a211 * a211) + 2);
			a395 = 0;
			a211 = 1;
		} else {

		}
	}
}
void calculate_outputm196(int input) {
	if ((((((-10 < a13) && (203 >= a13)) && (a312 == 33 && ((((cf == 1 && a75 == 36) && (35 == a46[2])) && a256 == 33) && a357 <= -188))) && input == inputs[0]) && (a207 == 33 && (((37 == a392[3]) && a329 == 33) && a146 == 1)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a162 -= (a162 - 20) < a162 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		cf = 0;
		if (a184 == 15) {
			a7 = 0;
			a75 = 32;
			a173 = 34;
			a172 = ((a270 / a359) - -3);
		} else {
			a286 = a294[6];
			a336 = 1;
			a172 = (a359 - -2);
			a270 = 13;
			a383 = a226[0];
			a382 = (((a382 / 5) + 16603) - -326);
			a338 = 7;
			a307 = a227[6];
			a235 = a216[2];
			a265 = a376;
			a173 = 34;
			a320 = 10;
			a333 = (((((43 * 9) / 10) - -63) * 10) / 9);
			a249 = ((((a249 % 71) + 428) + 1) + -2);
			a395 = 1;
			a234 = a372[5];
			a353 = a263;
			a260 = 1;
			a218 = 33;
			a256 = 33;
			a392 = a304;
			a329 = 36;
			a240 = 1;
			a386 = ((((a386 % 14837) + 15162) + 1) + 0);
			a206 = 4;
			a239 = a268;
			a370 = a318;
			a202 = a217[4];
			a357 = (((((a357 / 5) / 5) * 5) % 38) - 1);
			a224 = 36;
			a310 = (((a310 - 0) / 5) - 10225);
			a300 = 1;
			a398 = 14;
			a269 = 33;
			a201 = (((a201 + 30185) + -24912) + 24919);
			a358 = a335;
			a276 = a253;
			a207 = 35;
			a313 = 35;
			a277 = (((((a277 - 0) / 5) * 5) % 95) - -317);
			a211 = 8;
			a228 = a229;
			a75 = 32;
			a373 = 1;
			a368 = 1;
			a237 = 6;
			a105 = 33;
			a324 = a232[3];
			a339 = 1;
			a359 = 5;
		}
	}
	if ((((35 == a46[2]) && ((a307 == a227[0] && (((a146 == 1 && cf == 1) && ((-10 < a13) && (203 >= a13))) && input == inputs[5])) && a359 == 3)) && ((a234 == a372[0] && ((a269 == 33 && a207 == 33) && a75 == 36)) && a243 <= -179))) {
		a165 -= (a165 - 20) < a165 ? 3 : 0;
		a63 -= (a63 - 20) < a63 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if (((((a66 == 1 || (11 == a353[4])) || !(15 == a353[2])) || a191 == a37[3]) && !(a105 == 34))) {
			a240 = 0;
			a378 = 0;
			a132 = 0;
			a324 = a232[6];
			a265 = a376;
			a235 = a216[4];
			a302 = a346[1];
			a277 = ((((a277 * 1) % 14995) + -10) - 520);
			a329 = 34;
			a358 = a351;
			a382 = ((((a382 % 14911) + 15087) * 1) - -2587);
			a383 = a226[2];
			a296 = a384;
			a75 = 33;
			a16 = 1;
			a361 = 36;
			a333 = ((((95 + 73) * 5) + 4217) - 4889);
			a225 = a205[2];
			a300 = 1;
			a77 = ((a230 + a338) + 3);
		} else {
			a130 = (((((a13 * a13) % 14999) / 5) + 12580) - -5087);
			a201 = ((((a201 - 0) - 0) % 14900) - 199);
			a329 = 33;
			a357 = ((((a357 * 1) * -2) / 10) + 12646);
			a237 = 9;
			a211 = 7;
			a240 = 1;
			a256 = 33;
			a339 = 1;
			a300 = 1;
			a373 = 1;
			a173 = 33;
			a312 = 35;
			a276 = a250;
			a206 = 6;
			a286 = a294[3];
			a370 = a318;
			a249 = ((((a249 % 71) - -428) / 5) - -321);
			a265 = a303;
			a324 = a232[3];
			a75 = 32;
			a207 = 35;
			a382 = (((((a382 - 0) - 0) - 0) % 14911) + 15087);
			a398 = 12;
			a218 = 34;
			a243 = ((((a243 * 1) / 5) * 5) + 30170);
			a368 = 1;
			a333 = (((10 + 3337) - -8545) + -4421);
			a13 = ((((((a13 * a386) % 14999) / 5) % 60) - -263) - 0);
			a270 = 10;
			a269 = 35;
			a353 = a399;
			a307 = a227[0];
			a234 = a372[2];
			a224 = 34;
			a202 = a217[6];
			a359 = 10;
			a228 = a292;
			a310 = ((((a310 % 20) - -336) - -1) - 1);
			a302 = a346[0];
			a313 = 34;
			a277 = ((((((a277 % 14995) + -10) * 1) - -18307) * -1) / 10);
			a383 = a226[5];
			a392 = a208;
			a230 = 5;
			a395 = 0;
			a239 = a242;
			a225 = a205[6];
			a260 = 1;
			a338 = 8;
			a235 = a216[4];
			a386 = (((((a386 * 1) % 14837) + 15162) - 4150) - -4151);
		}
	}
	if ((((a75 == 36 && (a312 == 33 && a313 == 33)) && ((-10 < a13) && (203 >= a13))) && ((((35 == a46[2]) && ((((cf == 1 && a146 == 1) && input == inputs[6]) && (36 == a239[5])) && a302 == a346[0])) && a256 == 33) && a260 == 1))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a63 -= (a63 - 20) < a63 ? 2 : 0;
		a133 -= (a133 - 20) < a133 ? 3 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		cf = 0;
		if ((a183 == 35 && ((!(a91 == 14) || a313 == 32) && a256 == 32))) {
			a206 = 11;
			a353 = a263;
			a286 = a294[5];
			a300 = 0;
			a320 = 13;
			a265 = a303;
			a358 = a351;
			a75 = 34;
			a249 = (((((a249 + 0) % 14750) - -15249) / 5) - -23662);
			a361 = 32;
			a373 = 1;
			a398 = 15;
			a296 = a212;
			a237 = 6;
			a57 = ((a270 - a359) + 9);
			a278 = a326[(a57 - 13)];
			a395 = 0;
			a313 = 36;
			a218 = 36;
			a201 = (((a201 - -30186) - -8) * 1);
			a240 = 0;
			a277 = ((((a277 - 0) % 14830) + 15169) * 1);
			a383 = a226[1];
			a329 = 35;
			a370 = a285;
			a368 = 0;
			a302 = a346[4];
			a239 = a299;
			a184 = a157[(a338 - 1)];
			a202 = a217[0];
			a243 = (((a243 * 1) / -5) + 10815);
			a378 = 0;
			a359 = 7;
			a336 = 0;
			a357 = (((a357 + 30175) + 6) - -6);
			a235 = a216[3];
			a312 = 33;
			a338 = 8;
			a230 = 3;
			a310 = ((((a310 / 5) % 77) - -237) * 1);
			a269 = 36;
			a386 = ((((a386 % 14837) + 15162) * 1) - -1);
			a339 = 1;
			a211 = 7;
			a224 = 33;
			a260 = 0;
			a276 = a289;
			a307 = a227[3];
			a324 = a232[2];
			a225 = a205[4];
			a256 = 35;
			a234 = a372[5];
			a382 = (((((a382 % 14967) + -65) - 10080) * 10) / 9);
			a392 = a304;
			a270 = 15;
		} else {
			a333 = (((((69 * 5) * 5) + -24238) * -1) / 10);
			a277 = (((((a277 % 14830) - -15169) * 10) / 9) * 1);
			a368 = 1;
			a276 = a250;
			a201 = (((((a201 - 0) - 0) + 0) * -9) / 10);
			a206 = 7;
			a383 = a226[0];
			a207 = 36;
			a357 = (((((a357 % 14906) + -188) * 10) / 9) - 58);
			a296 = a362;
			a237 = 6;
			a234 = a372[5];
			a329 = 36;
			a324 = a232[2];
			a243 = ((((a243 % 14910) + -179) * 1) - 3794);
			a320 = 11;
			a202 = a217[4];
			a218 = 35;
			a307 = a227[5];
			a373 = 1;
			a302 = a346[3];
			a336 = 1;
			a249 = (((a249 / 5) / 5) - 21375);
			a239 = a299;
			a370 = a318;
			a313 = 36;
			a353 = a263;
			a269 = 34;
			a286 = a294[4];
			a395 = 1;
			a270 = 17;
			a260 = 1;
			a230 = 8;
			a129 = a92[(a398 + -5)];
			a339 = 1;
			a392 = a208;
			a359 = 3;
			a310 = ((((((a310 % 20) - -337) - 2756) * 5) % 20) - -342);
			a75 = 32;
			a235 = a216[7];
			a338 = 9;
			a382 = (((((a382 - -370) / 5) * 5) % 14911) + 15087);
			a265 = a293;
			a173 = 32;
			a240 = 1;
			a125 = a30[7];
			a256 = 36;
			a211 = 1;
			a386 = (((((a386 + 6547) - 4821) - 1265) % 61) + 262);
			a228 = a229;
			a300 = 1;
			a312 = 36;
			a398 = 10;
		}
	}
	if ((((a146 == 1 && (a300 == 1 && (a339 == 1 && (((98 == a276[2]) && a201 <= -199) && ((-10 < a13) && (203 >= a13)))))) && a336 == 1) && (input == inputs[9] && (((35 == a46[2]) && (a75 == 36 && cf == 1)) && a368 == 1)))) {
		a165 += (a165 + 20) > a165 ? 2 : 0;
		a89 += (a89 + 20) > a89 ? 3 : 0;
		a174 += (a174 + 20) > a174 ? 3 : 0;
		a133 -= (a133 - 20) < a133 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a93 += (a93 + 20) > a93 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 1 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		if (((!(a256 == 33) && (a134 == 1 || (cf != 1 || a383 == a226[3]))) || a184 == a157[1])) {
			a235 = a216[1];
			a239 = a299;
			a170 = (((((a277 * a386) % 14999) - 14986) - 11) - 2);
			a230 = 6;
			a270 = 16;
			a218 = 35;
			a81 = a167[(a359 - -2)];
			a207 = 35;
			a224 = 33;
			a358 = a348;
			a392 = a257;
			a357 = (((a357 + 30069) + 49) - -31);
			a201 = ((((a201 + 8107) % 14900) - 15098) - 0);
			a307 = a227[7];
			a312 = 33;
			a202 = a217[1];
			a378 = 0;
			a370 = a285;
			a57 = (a320 + 6);
			a225 = a205[5];
			a395 = 0;
			a353 = a241;
			a206 = 4;
			a234 = a372[6];
			a336 = 0;
			a373 = 1;
			a359 = 3;
			a361 = 32;
			a75 = 34;
			a300 = 0;
			a386 = (((((a386 * 1) + 12060) / 5) % 61) + 140);
			a276 = a289;
			a260 = 0;
			a368 = 0;
			a329 = 36;
			a320 = 13;
			a382 = ((((a382 / 5) % 12) - 43) * 1);
			a383 = a226[1];
			a265 = a293;
			a249 = (((((a249 % 14750) + 15249) / 5) / 5) - -6639);
			a302 = a346[5];
			a240 = 0;
			a243 = (((a243 / 5) + -7119) + -14147);
			a296 = a384;
			a398 = 10;
			a286 = a294[0];
			a338 = 10;
			a324 = a232[1];
			a211 = 2;
			a339 = 1;
			a256 = 32;
			a228 = a229;
			a237 = 4;
			a310 = (((((a310 / 5) / 5) * 5) % 20) - -337);
			a313 = 33;
			a277 = ((((a277 % 14995) - 10) + 2365) - 12751);
		} else {
			a75 = 32;
			a173 = 32;
			a125 = a30[3];
			a397 = 11;
		}
	}
	if (((a146 == 1 && ((37 == a392[3]) && (((-10 < a13) && (203 >= a13)) && (a336 == 1 && (a270 == 10 && (24 == a370[2])))))) && (a395 == 1 && (a75 == 36 && (a307 == a227[0] && (input == inputs[2] && ((35 == a46[2]) && cf == 1))))))) {
		a165 += (a165 + 20) > a165 ? 3 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a98 += (a98 + 20) > a98 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a51 += (a51 + 20) > a51 ? 4 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a143 = 36;
		a75 = 34;
		a69 = 36;
		a57 = ((a237 + a211) - -7);
	}
	if (((a146 == 1 && (a313 == 33 && (a75 == 36 && ((((-10 < a13) && (203 >= a13)) && cf == 1) && (35 == a46[2]))))) && ((a373 == 1 && (((a382 <= -65 && a234 == a372[0]) && input == inputs[4]) && (36 == a239[5]))) && a357 <= -188))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a12 -= (a12 - 20) < a12 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a98 -= (a98 - 20) < a98 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 3 : 0;
		a181 += (a181 + 20) > a181 ? 3 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a320 = 6;
		a1 = a87[((a398 + a206) - 11)];
		a201 = ((((a201 % 94) + 117) / 5) - 9);
		a370 = a318;
		a239 = a268;
		a218 = 36;
		a392 = a304;
		a211 = 3;
		a307 = a227[6];
		a240 = 1;
		a395 = 1;
		a173 = 35;
		a313 = 33;
		a310 = ((((a310 % 15080) - 14919) * 1) + -1);
		a269 = 35;
		a270 = 16;
		a353 = a399;
		a357 = (((((a357 + 0) + 0) - -22883) % 38) + -18);
		a75 = 32;
		a382 = ((((a382 % 14911) - -15087) - -4406) * 1);
		a91 = (a237 - -8);
	}
	if ((((a286 == a294[0] && (input == inputs[3] && (((45 == a228[1]) && a395 == 1) && a75 == 36))) && a313 == 33) && ((a339 == 1 && (a201 <= -199 && (a146 == 1 && (cf == 1 && ((-10 < a13) && (203 >= a13)))))) && (35 == a46[2])))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 += (a165 + 20) > a165 ? 1 : 0;
		a169 -= (a169 - 20) < a169 ? 3 : 0;
		a133 += (a133 + 20) > a133 ? 2 : 0;
		a50 -= (a50 - 20) < a50 ? 2 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 1 : 0;
		a156 += (a156 + 20) > a156 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		if (a237 == 5) {
			a361 = 32;
			a228 = a292;
			a329 = 36;
			a359 = 7;
			a201 = (((a201 / 5) + -18210) + -4393);
			a320 = 9;
			a392 = a304;
			a398 = 14;
			a237 = 6;
			a239 = a242;
			a353 = a399;
			a357 = (((((a357 * 1) % 38) + 1) + 11834) + -11841);
			a300 = 0;
			a125 = a30[(a206 + -3)];
			a313 = 36;
			a378 = 0;
			a270 = 13;
			a240 = 1;
			a310 = ((((a310 * 1) % 15080) - 14919) + -2);
			a249 = ((((a249 % 14750) + 15249) / 5) * 5);
			a235 = a216[7];
			a395 = 1;
			a230 = 5;
			a370 = a318;
			a312 = 36;
			a336 = 0;
			a307 = a227[4];
			a260 = 1;
			a256 = 32;
			a382 = ((((a382 + 0) - 0) % 14911) - -15087);
			a333 = (((54 - -11340) + -11265) - 150);
			a339 = 1;
			a324 = a232[7];
			a211 = 4;
			a265 = a376;
			a75 = 32;
			a368 = 0;
			a302 = a346[3];
			a243 = (((a243 + 0) - -30098) * 1);
			a207 = 33;
			a373 = 0;
			a173 = 32;
			a386 = ((((a386 % 15038) + -14960) - -16844) + -16845);
			a277 = ((((a277 + 10399) / 5) % 95) - -243);
			a286 = a294[3];
			a269 = 35;
			a206 = 7;
			a338 = 5;
			a276 = a250;
			a218 = 32;
			a202 = a217[4];
			a234 = a372[4];
			a224 = 35;
			a8 = 11;
		} else {
			a75 = 32;
			a125 = a30[(a398 - 5)];
			a173 = 32;
			a81 = a167[(a237 - -2)];
		}
	}
	if (((a310 <= 160 && ((((a302 == a346[0] && ((a240 == 1 && a235 == a216[0]) && a146 == 1)) && ((-10 < a13) && (203 >= a13))) && input == inputs[8]) && (45 == a228[1]))) && (a324 == a232[0] && (((35 == a46[2]) && cf == 1) && a75 == 36)))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 2 : 0;
		a12 += (a12 + 20) > a12 ? 1 : 0;
		a50 += (a50 + 20) > a50 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 += (a90 + 20) > a90 ? 3 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 1 : 0;
		cf = 0;
		if (258 < a72) {
			a218 = 35;
			a296 = a384;
			a249 = (((((a249 * 1) % 101) - -254) / 5) - -209);
			a333 = (((36 - -25785) - -916) * 1);
			a134 = 1;
			a310 = ((((a310 % 15080) + -14919) / 5) - 7170);
			a75 = 35;
			a358 = a351;
			a201 = (((((a201 / 5) % 94) + 116) - -25105) + -25088);
			a196 = (a398 + 7);
			a378 = 0;
			a361 = 32;
			a202 = a217[7];
			a235 = a216[3];
			a313 = 35;
			a286 = a294[5];
			a383 = a226[4];
			a302 = a346[4];
			a357 = (((a357 / 5) - 369) - 5623);
			a91 = ((a196 + a196) - 21);
		} else {
			a224 = 35;
			a338 = 6;
			a240 = 1;
			a320 = 12;
			a265 = a303;
			a218 = 33;
			a270 = 10;
			a313 = 33;
			a310 = (((((a310 % 20) - -336) * 5) % 20) + 324);
			a75 = 32;
			a357 = ((((a357 / 5) * 10) / -9) + 7422);
			a373 = 1;
			a172 = (a398 - 6);
			a312 = 35;
			a392 = a304;
			a368 = 1;
			a370 = a318;
			a395 = 1;
			a260 = 1;
			a173 = 34;
			a302 = a346[2];
			a274 = a290;
		}
	}
	if (((a249 <= 152 && a202 == a217[0]) && (((-10 < a13) && (203 >= a13)) && (input == inputs[7] && (a75 == 36 && ((a357 <= -188 && ((a300 == 1 && (a146 == 1 && ((35 == a46[2]) && cf == 1))) && a256 == 33)) && (3 == a353[2]))))))) {
		a131 += (a131 + 20) > a131 ? 1 : 0;
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a89 -= (a89 - 20) < a89 ? 1 : 0;
		a63 -= (a63 - 20) < a63 ? 2 : 0;
		a50 += (a50 + 20) > a50 ? 2 : 0;
		a98 -= (a98 - 20) < a98 ? 3 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a181 -= (a181 - 20) < a181 ? 2 : 0;
		cf = 0;
		a16 = 0;
		a146 = 0;
		a73 = ((((((a13 * a13) % 14999) % 54) + 223) * 1) * 1);
	}
	if (((a398 == 10 && (a256 == 33 && ((a307 == a227[0] && (a373 == 1 && (24 == a370[2]))) && a206 == 4))) && (a75 == 36 && ((((35 == a46[2]) && (cf == 1 && a146 == 1)) && input == inputs[1]) && ((-10 < a13) && (203 >= a13)))))) {
		a165 -= (a165 - 20) < a165 ? 1 : 0;
		a56 += (a56 + 20) > a56 ? 1 : 0;
		a90 -= (a90 - 20) < a90 ? 1 : 0;
		a110 += (a110 + 20) > a110 ? 1 : 0;
		a181 += (a181 + 20) > a181 ? 2 : 0;
		a88 += (a88 + 20) > a88 ? 1 : 0;
		cf = 0;
		a75 = 32;
		a173 = 36;
		a141 = a47[2];
		a244 = a363[0];
	}
}
void calculate_outputm18(int input) {
	if (((a307 == a227[0] && (cf == 1 && (27 == a46[0]))) && ((((a277 <= -10 && a373 == 1) && a234 == a372[0]) && a383 == a226[0]) && a225 == a205[0]))) {
		if (((a270 == 10 && (a313 == 33 && ((3 == a353[2]) && (a313 == 33 && a307 == a227[0])))) && ((a151 == 1 && cf == 1) && a333 <= -47))) {
			calculate_outputm195(input);
		}
	}
	if ((((cf == 1 && (35 == a46[2])) && (47 == a265[5])) && ((a329 == 33 && ((a324 == a232[0] && (45 == a228[1])) && a339 == 1)) && a207 == 33))) {
		if ((((((-10 < a13) && (203 >= a13)) && cf == 1) && a373 == 1) && ((47 == a265[5]) && (a243 <= -179 && ((a224 == 33 && a398 == 10) && a338 == 3))))) {
			calculate_outputm196(input);
		}
	}
}
void calculate_outputm199(int input) {
	if (((a336 == 1 && (a75 == 36 && ((a146 != 1 && cf == 1) && a16 == 1))) && ((a324 == a232[0] && ((((((167 < a73) && (277 >= a73)) && a395 == 1) && input == inputs[8]) && a277 <= -10) && (45 == a228[1]))) && a378 == 1))) {
		a63 -= (a63 - 20) < a63 ? 1 : 0;
		cf = 0;
		a224 = 32;
		a256 = 32;
		a353 = a241;
		a329 = 32;
		a207 = 32;
		a276 = a289;
		a173 = 34;
		a75 = 32;
		a339 = 0;
		a239 = a268;
		a312 = 32;
		a286 = a294[1];
		a359 = 4;
		a296 = a384;
		a302 = a346[((a359 - a359) - -1)];
		a230 = a359;
		a338 = a359;
		a240 = 0;
		a172 = 1;
		a398 = (a230 + 7);
		a243 = ((((((a243 * a333) % 14999) - -701) % 11) + -176) - 1);
		a235 = a216[((a230 + a230) + -7)];
		a225 = a205[(a237 - 2)];
		a395 = 0;
		a336 = 0;
		a237 = ((a359 * a359) - 12);
		a324 = a232[(a270 - 8)];
		a378 = 0;
		a202 = a217[0];
		a270 = (a359 - -7);
		a368 = 0;
		a218 = 32;
		a300 = 0;
		a206 = (a398 + -6);
		a249 = (((((((a73 * a357) % 14999) - 6970) % 101) + 349) / 5) - -128);
		a386 = (((((((a386 * a277) % 14999) * 2) + -3) * 1) % 61) - -140);
		a260 = 0;
		a234 = a372[((a359 / a359) + -1)];
		a383 = a226[(a320 + -5)];
		a361 = 32;
		a265 = a293;
		a211 = (a230 - 3);
		a277 = (((((a382 * a382) * 5) % 95) - -180) - -60);
		a357 = (((((((a357 * a310) % 14999) % 65) + -122) - -1) / 5) + -91);
		a129 = a92[a172];
		a333 = ((((((a333 * a249) % 14999) - 12055) % 96) + 92) - 30);
	}
	if ((((((a146 != 1 && cf == 1) && ((167 < a73) && (277 >= a73))) && (67 == a358[2])) && a368 == 1) && (((((a373 == 1 && (a324 == a232[0] && input == inputs[3])) && a243 <= -179) && a243 <= -179) && a16 == 1) && a75 == 36))) {
		cf = 0;
		a224 = 34;
		a359 = ((a338 - a206) + 6);
		a265 = a376;
		a234 = a372[(a398 - 8)];
		a256 = 34;
		a276 = a250;
		a300 = 1;
		a202 = a217[(a230 + -2)];
		a286 = a294[(a270 + -8)];
		a302 = a346[(a270 + -8)];
		a249 = ((((((a386 * a243) % 14999) * 2) % 71) + 427) - 1);
	}
	if ((((a146 != 1 && (((a235 == a216[0] && (a243 <= -179 && a329 == 33)) && (67 == a358[2])) && a75 == 36)) && (a398 == 10 && ((a16 == 1 && (((167 < a73) && (277 >= a73)) && (cf == 1 && input == inputs[7]))) && a277 <= -10))) && a168 <= -13)) {
		a122 -= (a122 - 20) < a122 ? 1 : 0;
		cf = 0;
		a353 = a241;
		a357 = (((((((a357 * a243) % 14999) + -11157) % 65) - 121) - 19092) - -19090);
		a270 = (a237 + 8);
		a239 = a299;
		a240 = 0;
		a395 = 0;
		a91 = (a206 - -7);
		a218 = 32;
		a75 = 32;
		a361 = 32;
		a173 = 35;
		a1 = a87[(a91 - 8)];
	}
	if (((a361 == 33 && ((((cf == 1 && ((167 < a73) && (277 >= a73))) && a146 != 1) && a16 == 1) && (45 == a228[1]))) && ((a373 == 1 && (((input == inputs[6] && a339 == 1) && a339 == 1) && a75 == 36)) && a383 == a226[0]))) {
		cf = 0;
		if (((a302 == a346[0] && a57 == 10) || !(a320 == 11))) {
			a382 = (((1 - 7732) - -9203) - 1361);
			a239 = a268;
			a218 = 34;
			a277 = (((((((a277 * a382) % 14999) % 95) - -243) / 5) / 5) - -288);
			a361 = 34;
			a383 = a226[(a338 + -1)];
			a312 = 34;
			a57 = (a230 + 13);
			a211 = a338;
			a269 = 34;
			a329 = 34;
			a206 = (a230 - -3);
			a370 = a311;
			a235 = a216[((a359 - a359) + 1)];
			a240 = 1;
			a333 = ((((((((a333 * a73) % 14999) % 14) + 162) * 5) * 5) % 14) - -157);
			a310 = (((((((a382 * a277) % 14999) / 5) * 5) / 5) % 20) + 336);
			a395 = 1;
			a225 = a205[(a398 - 8)];
			a307 = a227[(a338 + -1)];
			a243 = ((((((a243 * a357) % 14999) % 43) + -138) - -11549) - 11555);
			a320 = (a359 + 3);
			a373 = 0;
			a368 = 1;
			a324 = a232[((a338 - a206) + 4)];
			a357 = (((((((a382 * a310) % 14999) * 2) % 38) + -17) - 12697) + 12696);
			a230 = (a338 - -2);
			a336 = 1;
			a296 = a362;
			a353 = a399;
			a358 = a335;
			a75 = 34;
			a278 = a326[(a57 - 13)];
			a386 = ((((((a386 * a249) % 14999) * 2) + -2) % 61) - -262);
			a237 = ((a338 + a206) + -4);
			a184 = a157[(a270 + -8)];
			a270 = (a338 - -9);
			a260 = 1;
			a398 = ((a320 / a211) + 10);
			a339 = 0;
			a338 = ((a57 * a206) + -91);
		} else {
			a386 = ((((((a386 * a277) % 14999) / 5) % 61) + 138) * 1);
			a395 = 0;
			a218 = 32;
			a383 = a226[((a206 * a237) - 10)];
			a333 = (((((((a333 * a357) % 14999) - 10378) % 96) - -51) - -24187) - 24188);
			a277 = ((((((a386 * a386) % 14999) - -7875) + -20037) % 95) - -243);
			a324 = a232[(a206 - 3)];
			a373 = 0;
			a378 = 0;
			a312 = 32;
			a243 = (((((((a243 * a201) % 14999) % 43) - 150) - -19) * 9) / 10);
			a286 = a294[((a270 + a398) - 19)];
			a228 = a264;
			a239 = a268;
			a249 = ((((((((a310 * a310) % 14999) % 101) + 254) * 9) / 10) + -17806) + 17734);
			a260 = 0;
			a353 = a399;
			a338 = (a230 - -1);
			a398 = (a237 + 9);
			a270 = ((a230 + a230) + 5);
			a276 = a289;
			a240 = 0;
			a300 = 0;
			a224 = 33;
			a302 = a346[(a211 + -1)];
			a358 = a351;
			a329 = 32;
			a357 = ((((((a382 * a73) / 5) % 65) - 60) * 10) / 9);
			a361 = 32;
			a339 = 0;
			a207 = 32;
			a368 = 0;
			a125 = a30[(a206 - -3)];
			a129 = a92[5];
			a225 = a205[(a230 + -2)];
			a237 = ((a338 + a338) + -4);
			a359 = (a320 - 3);
			a336 = 0;
			a230 = a206;
			a235 = a216[(a206 - 3)];
			a75 = 32;
			a173 = 32;
			a206 = (a211 - -3);
		}
	}
}
void calculate_outputm19(int input) {
	if ((((a378 == 1 && a333 <= -47) && a207 == 33) && (a386 <= 77 && (a386 <= 77 && ((3 == a353[2]) && (cf == 1 && ((167 < a73) && (277 >= a73)))))))) {
		if ((((cf == 1 && a16 == 1) && (45 == a228[1])) && (a336 == 1 && (a243 <= -179 && ((a312 == 33 && a225 == a205[0]) && a206 == 4))))) {
			calculate_outputm199(input);
		}
	}
}

void calculate_output(int input) {
	cf = 1;

	if ((((24 == a370[2]) && a260 == 1) && ((3 == a353[2]) && (a269 == 33 && ((67 == a358[2]) && (a230 == 3 && (cf == 1 && a75 == 33))))))) {
		if ((((((24 == a370[2]) && (a378 == 1 && a329 == 33)) && a235 == a216[0]) && a329 == 33) && ((45 == a228[1]) && (cf == 1 && a132 == 1)))) {
			calculate_outputm1(input);
		}
		if ((((a269 == 33 && (45 == a228[1])) && a310 <= 160) && (((98 == a276[2]) && ((cf == 1 && a132 != 1) && (36 == a239[5]))) && a218 == 33))) {
			calculate_outputm2(input);
		}
	}
	if (((((-188 < a357) && (-57 >= a357)) && ((160 < a310) && (316 >= a310))) && ((a313 == 32 && ((43 == a392[3]) && ((cf == 1 && a75 == 32) && a240 != 1))) && a270 == 11))) {
		if (((a240 != 1 && ((cf == 1 && a173 == 33) && a269 == 32)) && (((-10 < a277) && (148 >= a277)) && (a324 == a232[1] && (a206 == 5 && a378 != 1))))) {
			calculate_outputm3(input);
		}
		if ((((((28 == a370[0]) && a324 == a232[1]) && ((-199 < a201) && (-12 >= a201))) && a230 == 4) && (((a173 == 32 && cf == 1) && ((-65 < a382) && (-39 >= a382))) && (103 == a276[1])))) {
			calculate_outputm4(input);
		}
		if (((a338 == 4 && (a218 == 32 && (cf == 1 && a173 == 34))) && (a320 == 7 && ((a224 == 32 && a320 == 7) && a368 != 1)))) {
			calculate_outputm5(input);
		}
		if ((((a211 == 2 && (((a173 == 35 && cf == 1) && (43 == a392[3])) && a218 == 32)) && ((-188 < a357) && (-57 >= a357))) && (a269 == 32 && a269 == 32))) {
			calculate_outputm6(input);
		}
		if ((((43 == a392[3]) && (((-199 < a201) && (-12 >= a201)) && a260 != 1)) && ((a395 != 1 && (a329 == 32 && (cf == 1 && a173 == 36))) && a224 == 32))) {
			calculate_outputm7(input);
		}
	}
	if ((((a307 == a227[2] && ((a218 == 34 && a240 == 1) && a240 == 1)) && (15 == a353[2])) && ((a75 == 34 && cf == 1) && ((-57 < a357) && (20 >= a357))))) {
		if ((((a383 == a226[2] && (a207 == 34 && (a225 == a205[2] && (cf == 1 && a57 == 10)))) && a307 == a227[2]) && (a395 == 1 && a338 == 5))) {
			calculate_outputm8(input);
		}
		if ((((((-57 < a357) && (20 >= a357)) && (cf == 1 && a57 == 11)) && a230 == 5) && (a307 == a227[2] && ((a307 == a227[2] && ((-39 < a382) && (176 >= a382))) && ((-12 < a201) && (178 >= a201)))))) {
			calculate_outputm9(input);
		}
		if (((a378 == 1 && (cf == 1 && a57 == 12)) && (a230 == 5 && (((148 < a277) && (339 >= a277)) && ((a302 == a346[2] && ((355 < a249) && (499 >= a249))) && ((-156 < a243) && (-68 >= a243))))))) {
			calculate_outputm10(input);
		}
		if (((a339 != 1 && (a336 == 1 && (((59 == a228[3]) && a368 == 1) && (47 == a239[4])))) && ((a57 == 13 && cf == 1) && a329 == 34))) {
			calculate_outputm11(input);
		}
		if ((((a235 == a216[2] && (cf == 1 && a57 == 15)) && a206 == 6) && (((a218 == 34 && (110 == a276[2])) && a320 == 8) && (92 == a296[2])))) {
			calculate_outputm13(input);
		}
		if (((a395 == 1 && (a395 == 1 && (a256 == 34 && (a329 == 34 && (cf == 1 && a57 == 16))))) && (a336 == 1 && (47 == a239[4])))) {
			calculate_outputm14(input);
		}
	}
	if ((((45 == a228[1]) && ((a359 == 3 && (cf == 1 && a75 == 35)) && a339 == 1)) && ((98 == a276[2]) && (a333 <= -47 && a320 == 6)))) {
		if (((a338 == 3 && (a237 == 3 && (a134 == 1 && cf == 1))) && ((a373 == 1 && (a237 == 3 && a240 == 1)) && (45 == a228[1])))) {
			calculate_outputm16(input);
		}
		if (((a336 == 1 && (((a269 == 33 && (67 == a358[2])) && a218 == 33) && a202 == a217[0])) && ((cf == 1 && a134 != 1) && a224 == 33))) {
			calculate_outputm17(input);
		}
	}
	if (((a338 == 3 && (cf == 1 && a75 == 36)) && ((((a324 == a232[0] && a260 == 1) && a218 == 33) && (36 == a239[5])) && a398 == 10))) {
		if (((a307 == a227[0] && (cf == 1 && a146 == 1)) && ((a300 == 1 && (a359 == 3 && (a395 == 1 && a310 <= 160))) && a277 <= -10))) {
			calculate_outputm18(input);
		}
		if (((((a357 <= -188 && a339 == 1) && a240 == 1) && (81 == a296[3])) && (a237 == 3 && (a395 == 1 && (a146 != 1 && cf == 1))))) {
			calculate_outputm19(input);
		}
	}
	errorCheck();

	if (cf == 1) {
		ERR = ERR_INVALID_INPUT;
	}
}
