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
int v13 = nondet();
goto loc29;
loc29:
 if (nondet_bool()) {
  goto loc28;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc13;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  goto loc25;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  goto loc27;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  v3 = -1+v3;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v5 <= v8 )) goto end;
  v13 = nondet();
  v5 = 1+v5;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  v11 = 0;
  v1 = v11;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  v13 = nondet();
  v5 = 1+v3;
  goto loc4;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( v3 <= v5 )) goto end;
  v3 = 1+v3;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v3 )) goto end;
  v13 = nondet();
  v5 = 1+v5;
  goto loc11;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 1+v8 <= v3 )) goto end;
  v3 = -1+v8;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v3 <= v8 )) goto end;
  v13 = nondet();
  v5 = 0;
  goto loc11;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 1+v3 <= v6 )) goto end;
  v5 = 1+v5;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v6 <= v3 )) goto end;
  v13 = nondet();
  v6 = 1+v6;
  goto loc15;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  v3 = 1+v3;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( v5 <= v8 )) goto end;
  v13 = nondet();
  v6 = 0;
  goto loc15;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc0;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( v3 <= v6 )) goto end;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v3 )) goto end;
  v13 = nondet();
  v6 = 1+v6;
  goto loc7;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  v6 = 0;
  goto loc7;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc19;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  v5 = 1+v3;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v5 <= v8 )) goto end;
  v13 = nondet();
  goto loc20;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( v8 <= v3 )) goto end;
  v3 = 1;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v8 )) goto end;
  v5 = 1+v3;
  goto loc0;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v12 = nondet();
  v4 = 1+v4;
  goto loc23;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v4 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  if (!( v4 <= v2 )) goto end;
  goto loc22;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  if (!( 1+v7 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc26;
 }
 if (nondet_bool()) {
  if (!( v4 <= v7 )) goto end;
  goto loc24;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  if (!( 1+v7 <= v2 )) goto end;
  v10 = v9;
  v8 = v7;
  v3 = 0;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( v2 <= v7 )) goto end;
  v12 = 0;
  v4 = 0;
  goto loc23;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  v9 = 50;
  v7 = 5;
  v2 = 0;
  goto loc26;
 }
 goto end;
loc6:
end:
;
}
