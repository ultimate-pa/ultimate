// #Unsafe
// Works with OneNontrivialStatement

procedure main() {
    var sortedArray : [int]int;
    var randomInt : int;    
    var lastInt : int;
    var counter : int;
    var length : int;

    havoc lastInt;
    havoc length;
    assume 0 < length && length <= 32;
    counter := 0;

    // Fill <length> array entries with rising values.
    while(counter < length) {
        havoc randomInt;
        assume lastInt <= randomInt;
        sortedArray[counter] := randomInt;
        lastInt := randomInt;
        counter := counter + 1;
    }

    counter := 0;

    // Read and check if <length + 1> array entries are sorted.
    // Final entry should be smaller in 50% of iterations, error.
    while(counter < length) {
        assert sortedArray[counter] <= sortedArray[counter + 1];
        counter := counter + 1;
    }
}