int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc30;
loc30:
 if (nondet_bool()) {
  goto loc28;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  v2 = -1+v2;
  v4 = v2;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  v4 = v2;
  goto loc11;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  v6 = -1+v6;
  v4 = v2;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  goto loc20;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  v5 = 1;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v2 = nondet();
  v3 = nondet();
  if (!( v4 <= v2 )) goto end;
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v3 = 1+v3;
  v4 = v2;
  goto loc4;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  v5 = 1;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v2 = nondet();
  v3 = nondet();
  if (!( v4 <= v2 )) goto end;
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = 0;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc7;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v1 = v6;
  v4 = v2;
  goto loc8;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  v5 = 1;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v2 = nondet();
  v3 = nondet();
  if (!( v4 <= v2 )) goto end;
  goto loc13;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = 0;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc14;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  v5 = 1;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  if (!( v4 <= v2 )) goto end;
  goto loc15;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v2 = nondet();
  v3 = nondet();
  if (!( v4 <= v2 )) goto end;
  goto loc16;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = 0;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc17;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  v5 = 1;
  goto loc21;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  goto loc21;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  v2 = nondet();
  v3 = nondet();
  if (!( v4 <= v2 )) goto end;
  goto loc22;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = 0;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc23;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  goto loc18;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  v5 = 1;
  goto loc24;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  goto loc24;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  v2 = nondet();
  v3 = nondet();
  if (!( v4 <= v2 )) goto end;
  goto loc25;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = 0;
  goto loc26;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc26;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  v2 = 1;
  v3 = 0;
  v1 = nondet();
  v6 = nondet();
  if (!( 1 <= v6 )) goto end;
  v4 = v2;
  goto loc27;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v6 <= v1 )) goto end;
  goto loc29;
 }
 if (nondet_bool()) {
  goto loc18;
 }
 goto end;
loc29:
loc20:
end:
;
}
