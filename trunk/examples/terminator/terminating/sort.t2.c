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
int v12 = nondet();
goto loc26;
loc26:
 if (nondet_bool()) {
  goto loc25;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc19;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  goto loc24;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v12 = 0;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v12 = 1;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v12 = 1;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v3 = v11;
  v5 = 1+v5;
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v11 = 1;
  goto loc5;
 }
 if (nondet_bool()) {
  v11 = 0;
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v11 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( -1+v4 <= v5 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= -1+v4 )) goto end;
  goto loc8;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v1 = v10;
  v5 = 1+v5;
  goto loc13;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v10 = 1;
  goto loc12;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v10 = 0;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v10 = 0;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc15;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v9 = 0;
  goto loc18;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  goto loc17;
 }
 if (nondet_bool()) {
  v9 = 1;
  goto loc18;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  v2 = v9;
  v6 = 1+v6;
  goto loc21;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v9 = 1;
  goto loc18;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc22;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  if (!( v4 <= v6 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v4 )) goto end;
  goto loc23;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( v4 <= v5 )) goto end;
  v5 = 0;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  v2 = 0;
  v6 = 0;
  goto loc21;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( v4 <= v5 )) goto end;
  v5 = 0;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  v5 = 1+v5;
  goto loc10;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  v1 = 1;
  v3 = 1;
  v4 = 10;
  v7 = nondet();
  v8 = nondet();
  v5 = 0;
  goto loc10;
 }
 goto end;
loc1:
end:
;
}
