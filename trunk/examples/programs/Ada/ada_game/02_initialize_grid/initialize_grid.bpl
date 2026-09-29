var ROWS: int;
var COLS: int;

var Grid_Danger: [int, int] bool;

procedure Initialize_Grid()
   modifies Grid_Danger;
   requires ROWS == 5 && COLS == 20;
{
   var r, c: int;
   r := 1;

   while (r <= ROWS)
   {
      c := 1;

      while (c <= COLS)
      {
         assert r >= 1 && r <= ROWS;
         assert c >= 1 && c <= COLS;

         Grid_Danger[r, c] := false;

         c := c + 1;
      }
      r := r + 1;
   }
}
