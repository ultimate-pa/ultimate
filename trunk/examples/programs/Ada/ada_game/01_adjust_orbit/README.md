# Idea 1: `Adjust_Orbit`

Boogie Model: [`adjust_orbit.bpl`](adjust_orbit.bpl)

## Original Ada

```ada
procedure Adjust_Orbit(ID : in Integer; Delta_Alt : in Integer; Delta_Spd : in Integer) with SPARK_Mode => On is
begin
   if ID in 1 .. Max_Satellites then
      Satellite_Positions(ID).Altitude := Satellite_Positions(ID).Altitude + Delta_Alt;
      Satellite_Positions(ID).Speed    := Satellite_Positions(ID).Speed + Delta_Spd;
   else
      null;
   end if;
end Adjust_Orbit;
```

## Modeling Idea

The Boogie model focuses purely on the given global states and implements exactly one procedure.

- The model exclusively uses `Sat_Altitude`, `Sat_Speed`, `Grid_Danger`, as well as the Jet variables. Global constants for arrays and grid boundaries are clearly defined (e.g., `Max_Satellites == 3`).
- Instead of separate helper functions, the invariants (altitude must be between 160 and 2000 km, speed must be positive) are enforced directly as `requires` preconditions.
- Within the implementation, read/write accesses are verified immediately using `assert`.

## Results from Ultimate PA

| Type | Description |
|---|---|
| Assertion always holds | `assert ID >= 1 && ID <= Max_Satellites;` |
| Assertion always holds | `assert Sat_Altitude[ID] == old_alt + Delta_Alt;` |
| Assertion always holds | `assert Sat_Speed[ID] == old_spd + Delta_Spd;` |
| Procedure Contract | `Modifies: [Sat_Altitude, Sat_Speed]` |

**Overall Result: All specifications hold — 3 specifications checked, all of them hold.**

### Plausibility Check of the Assertions and Contracts

- The precondition `requires ID >= 1 && ID <= Max_Satellites;` guarantees a valid index.
- The value update is performed via direct, linear code without loops. By saving the original values in `old_alt` and `old_spd`, Ultimate PA mathematically proves through the last two assertions that the operations `+ Delta_Alt` and `+ Delta_Spd` are applied flawlessly. Furthermore, the preconditions regarding the physical limits (160 to 2000 km altitude) ensure that these calculations do not result in any unexpected violations of the value range.
- The derived contract `Modifies: [Sat_Altitude, Sat_Speed]` confirms the desired behavior at the system level. There are no unintended side effects; critical external variables like `Grid_Danger` remain unaffected.