// based on https://de.wikipedia.org/wiki/Quicksort#Iteratives_Quicksort
procedure main() {
    var randomArray : [int]int;
    var stack : [int]int;

    var pivot : int;
    var left : int;
    var middle : int;
    var right : int;

    var index : int;
    var temp : int;
    var initialPass : bool; // used to enter the loop before anything is on the stack, and to continue the loop once more after taking off the last element.
    var elements : int;
    elements := 32;
    index := 0;

    while(index < elements) {
        havoc temp;
        randomArray[index] := temp;
        index := index + 1;
    }
    assert index == elements;

    left := 0;
    right := elements - 1;
    index := 0;
    initialPass := true;

    while(initialPass || 0 < index) {
        initialPass := false;
        while(left < right) {

            havoc temp;
            assume left <= temp && temp <= right;
            pivot := randomArray[temp];

            stack[index] := right;
            middle := left;
            index := index + 1;

            while(middle < right) {
                while(randomArray[middle] < pivot) {
                    middle := middle + 1;
                }
                while(pivot < randomArray[right]) {
                    right := right - 1;
                }
                if(middle < right) {
                    temp := randomArray[right];
                    randomArray[right] := randomArray[middle];
                    randomArray[middle] := temp;

                    right := right - 1;
                }
            }
        }
        left := right + 1;
        if(0 < index) {
            initialPass := true; // guarantee one more go should this be the last element
            index := index - 1;
            right := stack[index];
        }
    }
    
    index := 1;
    while(index < elements) {
        assert randomArray[index - 1] <= randomArray[index];
        index := index + 1;
    }
}