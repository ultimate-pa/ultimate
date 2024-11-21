/** Insertion Sort
 *
 * Given an array a and integers lo and hi,
 * returns an array that contains the same elements as a
 * except the values between lo and hi (inclusive)
 * have been sorted in ascending order.
 *
 * Author: Tanja Schindler, Dominik Klumpp
 * Date: 2019-06-05
 */

// We define two predicates that are used to express the loop invariants
// more compactly.

// ar is sorted between lo (incl.) and hi (incl.)
function sorted(ar : [int]int, lo : int, hi : int) : bool
{ (forall i1, i2 : int :: lo <= i1 && i1 <= i2 && i2 <= hi ==> ar[i1] <= ar[i2]) }

// all elements between lo1 (incl.) and hi1 (incl.) are less than or equal to
// all elements between lo2 (incl.) and hi2 (incl.).
function partitioned(ar : [int]int, lo1 : int, hi1 : int, lo2 : int, hi2 : int) : bool
{ (forall i1, i2 : int :: lo1 <= i1 && i1 <= hi1 && lo2 <= i2 && i2 <= hi2 ==> ar[i1] <= ar[i2]) }


procedure InsertionSort(lo : int, hi : int, a : [int]int) returns (ar : [int]int)
  requires lo <= hi;
  ensures sorted(ar, lo, hi);
{
     var i, j, temp : int;
     ar := a;
     i := lo+1;
     while (i <= hi)
       invariant sorted(ar, lo, i-1) && lo < i && i <= hi+1;
     {
         j := i;
         while (j > lo && ar[j] < ar[j-1])
           invariant sorted(ar, lo, j-1) && sorted(ar, j, i) && partitioned(ar, lo, j - 1, j + 1, i) && lo <= j && j <= i && i <= hi;
         {
             temp := ar[j-1];
             ar[j-1] := ar[j];
             ar[j] := temp;
             j := j-1;
         }
         i := i+1;
     }
}
