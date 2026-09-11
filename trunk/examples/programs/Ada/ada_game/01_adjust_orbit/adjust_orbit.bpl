var Rows: int where Rows == 5;
var Cols: int where Cols == 20;
var Max_Satellites: int where Max_Satellites == 3;

var Grid_Danger: [int, int] bool;

var Sat_Altitude: [int] int;
var Sat_Speed: [int] int;

var Jet_Row: int;
var Jet_Col: int;
var Jet_Vel: int;

procedure Adjust_Orbit(ID: int, Delta_Alt: int, Delta_Spd: int)
  modifies Sat_Altitude, Sat_Speed;
  
  requires ID >= 1 && ID <= Max_Satellites;
  requires Sat_Altitude[ID] + Delta_Alt >= 160 && Sat_Altitude[ID] + Delta_Alt <= 2000;
  requires Sat_Speed[ID] + Delta_Spd > 0;
{
  var old_alt: int;
  var old_spd: int;
  
  old_alt := Sat_Altitude[ID];
  old_spd := Sat_Speed[ID];
  
  assert ID >= 1 && ID <= Max_Satellites;
  
  Sat_Altitude[ID] := Sat_Altitude[ID] + Delta_Alt;
  Sat_Speed[ID] := Sat_Speed[ID] + Delta_Spd;
  
  assert Sat_Altitude[ID] == old_alt + Delta_Alt;
  assert Sat_Speed[ID] == old_spd + Delta_Spd;
}