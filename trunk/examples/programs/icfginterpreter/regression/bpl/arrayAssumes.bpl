// #Safe
// Works with SequenceOfStatements setting

procedure main() {
    var arr : [int]int;
    var valRecord : [int]int;
    var signRecord : [int]int;
    var rand1 : int;
    var rand2 : int;
    var counter : int;

    counter := 0;

    // Step one: Create restrictions for array entries
    while(counter < 32) {
        havoc rand1;
        havoc rand2;

        assume -1 <= rand1 && rand1 <= 1;
        assume -512 <= rand2 && rand2 <= 512;

        assert rand1 > -2; // split edge here to avoid having two havocs dependent on another
        
        if(rand1 == 0) {
            assume arr[counter] == rand2;
        }       
        else if(rand1 == -1) {
            assume arr[counter] < rand2;
        } 
        else {
            assume arr[counter] > rand2;
        }

        signRecord[counter] := rand1;
        valRecord[counter] := rand2;

        counter := counter + 1;
    }

    // Step two: Read array entries to execute havoc and check correctness
    counter := 0;
    while(counter < 32) {
        if(signRecord[counter] == 0) {
            assert arr[counter] == valRecord[counter];
        }       
        else if(signRecord[counter] == -1) {
            assert arr[counter] < valRecord[counter];
        } 
        else {
            assert arr[counter] > valRecord[counter];
        }
        counter := counter + 1;
    }
}