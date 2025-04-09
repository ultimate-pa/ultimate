// Given that the program currently uses longs, we know that the highest fibonacci
// number to be correctly calculated before overflow is the 92nd one, 7540113804746346429

procedure main() {
    var correctFibonacci : [int]int;
    var cache : [int]int;
    var highestIndex : int;
    var index : int;

    correctFibonacci[0] := 0;
    correctFibonacci[1] := 1;
    correctFibonacci[2] := 1;
    correctFibonacci[3] := 2;
    correctFibonacci[4] := 3;
    correctFibonacci[5] := 5;
    correctFibonacci[6] := 8;
    correctFibonacci[7] := 13;
    correctFibonacci[8] := 21;
    correctFibonacci[9] := 34;
    correctFibonacci[10] := 55;
    correctFibonacci[11] := 89;
    correctFibonacci[12] := 144;
    correctFibonacci[13] := 233;
    correctFibonacci[14] := 377;
    correctFibonacci[15] := 610;
    correctFibonacci[16] := 987;
    correctFibonacci[17] := 1597;
    correctFibonacci[18] := 2584;
    correctFibonacci[19] := 4181;
    correctFibonacci[20] := 6765;
    correctFibonacci[21] := 10946;
    correctFibonacci[22] := 17711;
    correctFibonacci[23] := 28657;
    correctFibonacci[24] := 46368;
    correctFibonacci[25] := 75025;
    correctFibonacci[26] := 121393;
    correctFibonacci[27] := 196418;
    correctFibonacci[28] := 317811;
    correctFibonacci[29] := 514229;
    correctFibonacci[30] := 832040;
    correctFibonacci[31] := 1346269;
    correctFibonacci[32] := 2178309;
    correctFibonacci[33] := 3524578;
    correctFibonacci[34] := 5702887;
    correctFibonacci[35] := 9227465;
    correctFibonacci[36] := 14930352;
    correctFibonacci[37] := 24157817;
    correctFibonacci[38] := 39088169;
    correctFibonacci[39] := 63245986;
    correctFibonacci[40] := 102334155;
    correctFibonacci[41] := 165580141;
    correctFibonacci[42] := 267914296;
    correctFibonacci[43] := 433494437;
    correctFibonacci[44] := 701408733;
    correctFibonacci[45] := 1134903170;
    correctFibonacci[46] := 1836311903;
    correctFibonacci[47] := 2971215073;
    correctFibonacci[48] := 4807526976;
    correctFibonacci[49] := 7778742049;
    correctFibonacci[50] := 12586269025;
    correctFibonacci[51] := 20365011074;
    correctFibonacci[52] := 32951280099;
    correctFibonacci[53] := 53316291173;
    correctFibonacci[54] := 86267571272;
    correctFibonacci[55] := 139583862445;
    correctFibonacci[56] := 225851433717;
    correctFibonacci[57] := 365435296162;
    correctFibonacci[58] := 591286729879;
    correctFibonacci[59] := 956722026041;
    correctFibonacci[60] := 1548008755920;
    correctFibonacci[61] := 2504730781961;
    correctFibonacci[62] := 4052739537881;
    correctFibonacci[63] := 6557470319842;
    correctFibonacci[64] := 10610209857723;
    correctFibonacci[65] := 17167680177565;
    correctFibonacci[66] := 27777890035288;
    correctFibonacci[67] := 44945570212853;
    correctFibonacci[68] := 72723460248141;
    correctFibonacci[69] := 117669030460994;
    correctFibonacci[70] := 190392490709135;
    correctFibonacci[71] := 308061521170129;
    correctFibonacci[72] := 498454011879264;
    correctFibonacci[73] := 806515533049393;
    correctFibonacci[74] := 1304969544928657;
    correctFibonacci[75] := 2111485077978050;
    correctFibonacci[76] := 3416454622906707;
    correctFibonacci[77] := 5527939700884757;
    correctFibonacci[78] := 8944394323791464;
    correctFibonacci[79] := 14472334024676221;
    correctFibonacci[80] := 23416728348467685;
    correctFibonacci[81] := 37889062373143906;
    correctFibonacci[82] := 61305790721611591;
    correctFibonacci[83] := 99194853094755497;
    correctFibonacci[84] := 160500643816367088;
    correctFibonacci[85] := 259695496911122585;
    correctFibonacci[86] := 420196140727489673;
    correctFibonacci[87] := 679891637638612258;
    correctFibonacci[88] := 1100087778366101931;
    correctFibonacci[89] := 1779979416004714189;
    correctFibonacci[90] := 2880067194370816120;
    correctFibonacci[91] := 4660046610375530309;
    correctFibonacci[92] := 7540113804746346429;



    cache[0] := 0;
    cache[1] := 1;
    highestIndex := 1;
    havoc index;
    assume 0 <= index && index <= 92;

    while(highestIndex < index) {
        cache[highestIndex + 1] := cache[highestIndex - 1] + cache[highestIndex];
        highestIndex := highestIndex + 1;
        assert (cache[highestIndex] == correctFibonacci[highestIndex]);
    }
}