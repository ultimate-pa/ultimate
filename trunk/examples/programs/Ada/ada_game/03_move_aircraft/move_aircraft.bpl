var ROWS: int;
var COLS: int;

var Grid_Danger: [int, int] bool;
var Jet_Row: int;
var Jet_Col: int;
var Jet_Vel: int;

procedure Move_Aircraft_Forward()
   modifies Jet_Col;
   requires ROWS == 5 && COLS == 20;

   requires Jet_Col >= 1 && Jet_Col <= COLS;
   requires Jet_Vel >= 1 && Jet_Vel <= 3;
   requires Jet_Row >= 1 && Jet_Row <= ROWS;

   ensures Jet_Col >= 1 && Jet_Col <= COLS + 1;
{
   var step: int;
   step := 1;

   while (step <= Jet_Vel)
   {
      Jet_Col := Jet_Col + 1;

      if (Jet_Col > COLS) {
         break;
      }

      assert Jet_Row >= 1 && Jet_Row <= ROWS;
      assert Jet_Col >= 1 && Jet_Col <= COLS;

      // simulating "if Grid(Jet.Row, Jet.Column).Danger"
      if (Grid_Danger[Jet_Row, Jet_Col]) {
         // Jet.Status := Damaged ...
      }

      step := step + 1;
   }
}

// Jet_Row := Jet_Row - 1 instead Climb-Logic below.
procedure Move_Aircraft_Climb()
   modifies Jet_Row, Jet_Col;
   requires ROWS == 5 && COLS == 20;

   requires Jet_Col >= 1 && Jet_Col <= COLS;
   requires Jet_Vel >= 1 && Jet_Vel <= 3;
   requires Jet_Row >= 1 && Jet_Row <= ROWS;

   ensures Jet_Col >= 1 && Jet_Col <= COLS + 1;
   ensures Jet_Row >= 1 && Jet_Row <= ROWS;
{
   var step: int;

   if (Jet_Row < ROWS) {
      Jet_Row := Jet_Row + 1;
   }

   assert Jet_Row >= 1 && Jet_Row <= ROWS;

   step := 1;
   while (step <= Jet_Vel)
   {
      Jet_Col := Jet_Col + 1;

      if (Jet_Col > COLS) {
         break;
      }

      assert Jet_Row >= 1 && Jet_Row <= ROWS;
      assert Jet_Col >= 1 && Jet_Col <= COLS;

      if (Grid_Danger[Jet_Row, Jet_Col]) {
         // Jet_Status := Damaged
      }

      step := step + 1;
   }
}
