/* 
 * Program from Exercise 5 of sheet 12 in the lecture on program verification.
 * https://swt.informatik.uni-freiburg.de/teaching/SS2019/program-verification
 * Task: find a loop invariant that is sufficient to prove that the program
 * satisfies the given precondition-postcondition pair.
 * 
 * Author: Tanja Schindler, Dominik Klumpp
 * Date: 2019-06-05
 */

procedure SelectionSort(lo : int, hi : int, a : [int]int) returns (ar : [int]int)
    requires lo <= hi;
    ensures (forall i1, i2 : int :: lo <= i1 && i1 <= i2 && i2 <= hi
                                    ==> ar[i1] <= ar[i2]);
{
    var i, k, min, tmp : int;
    ar := a;

    k := lo;
    while (k <= hi) {
        // Find the index of the minimal element between k and hi (inclusive)
        min := k;
        i := k + 1;
        while (i <= hi) {
            if (ar[i] < ar[min]) { min := i; }
            i := i + 1;
        }

        // Swap ar[k] and ar[min]
        tmp := ar[k];
        ar[k] := ar[min];
        ar[min] := tmp;

        k := k + 1;
    }
}
