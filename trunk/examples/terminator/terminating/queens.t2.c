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
goto loc27;
loc27:
 if (nondet_bool()) {
  goto loc26;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  goto loc19;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v10 = 0;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v10 = 1;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v10 = 1;
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
  v5 = 1+v5;
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v2 = v9;
  goto loc5;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v9 = 1;
  goto loc7;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v9 = 0;
  goto loc7;
 }
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v9 = 0;
  goto loc7;
 }
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v9 = 0;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v2 = v8;
  goto loc13;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  v8 = 1;
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  goto loc15;
 }
 if (nondet_bool()) {
  v8 = 0;
  goto loc14;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v8 = 0;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc16;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( v4 <= v5 )) goto end;
  if (!( v5 <= v4 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v5 )) goto end;
  goto loc17;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( v3 <= v5 )) goto end;
  v4 = 1+v4;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v3 )) goto end;
  goto loc20;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v1 = v7;
  v5 = 0;
  goto loc6;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  v7 = 1;
  goto loc22;
 }
 if (nondet_bool()) {
  v7 = 0;
  goto loc22;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  v7 = 0;
  goto loc22;
 }
 if (nondet_bool()) {
  goto loc23;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v7 = 0;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc24;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc24;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( v3 <= v4 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v3 )) goto end;
  goto loc25;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( v3 <= v4 )) goto end;
  v4 = 0;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v3 )) goto end;
  v4 = 1+v4;
  goto loc8;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  v3 = 9;
  v1 = 1;
  v2 = 1;
  v6 = nondet();
  v4 = 0;
  goto loc8;
 }
 goto end;
loc1:
end:
;
}
