int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
int v7 = nondet();
int v8 = nondet();
int v9 = nondet();
int v10 = nondet();
int v11 = nondet();
goto loc32;
loc32:
 if (nondet_bool()) {
  goto loc31;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  goto loc15;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  goto loc22;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  goto loc30;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 1+v7 <= v3 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v3 <= v7 )) goto end;
  v3 = 1+v3;
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v2 = nondet();
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  if (!( v7 <= v5 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v7 )) goto end;
  goto loc7;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( 1+v7 <= v6 )) goto end;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v6 <= v7 )) goto end;
  v2 = nondet();
  v6 = 1+v6;
  goto loc16;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( v5 <= v4 )) goto end;
  if (!( v4 <= v5 )) goto end;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v5 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  goto loc16;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc19;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  v1 = v2;
  v4 = v3;
  goto loc18;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  if (!( v5 <= v6 )) goto end;
  v11 = nondet();
  v2 = nondet();
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  v8 = nondet();
  v6 = 1+v6;
  goto loc23;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( 1+v7 <= v3 )) goto end;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( v3 <= v7 )) goto end;
  v8 = nondet();
  goto loc23;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( v3 <= v6 )) goto end;
  v3 = 1+v3;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v3 )) goto end;
  v8 = nondet();
  v6 = 1+v6;
  goto loc13;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( v5 <= v3 )) goto end;
  v1 = 0;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v5 )) goto end;
  v8 = nondet();
  goto loc13;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc24;
 }
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  goto loc9;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc26;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  goto loc25;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc0;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  if (!( v9 <= v1 )) goto end;
  goto loc28;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v9 )) goto end;
  v1 = v9;
  goto loc28;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc27;
 }
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  v10 = nondet();
  v9 = v10;
  goto loc29;
 }
 goto end;
loc30:
 if (nondet_bool()) {
  if (!( 1+v7 <= v3 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v3 <= v7 )) goto end;
  v1 = 0;
  goto loc0;
 }
 goto end;
loc31:
 if (nondet_bool()) {
  goto loc26;
 }
 goto end;
loc24:
end:
;
}
