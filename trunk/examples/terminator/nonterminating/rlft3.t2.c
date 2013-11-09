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
int v14 = nondet();
int v15 = nondet();
int v16 = nondet();
int v17 = nondet();
int v18 = nondet();
int v19 = nondet();
int v20 = nondet();
int v21 = nondet();
int v22 = nondet();
goto loc26;
loc26:
 if (nondet_bool()) {
  goto loc25;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc18;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc19:
 if (nondet_bool()) {
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
  if (!( 0 <= v11 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= -1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v11 <= -1 )) goto end;
  if (!( -1 <= v11 )) goto end;
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v14 = nondet();
  v4 = nondet();
  v3 = nondet();
  v5 = nondet();
  v6 = nondet();
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v13 = 2-v8+v16;
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( v8 <= 1 )) goto end;
  if (!( 1 <= v8 )) goto end;
  v13 = 1;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 2 <= v8 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 1 )) goto end;
  goto loc7;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v8 = 1+v8;
  goto loc9;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = nondet();
  v5 = nondet();
  v6 = nondet();
  goto loc6;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  v13 = nondet();
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( v8 <= 1 )) goto end;
  if (!( 1 <= v8 )) goto end;
  v13 = 1;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 2 <= v8 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 1 )) goto end;
  goto loc13;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( 2 <= v9 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= 1 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( v9 <= 1 )) goto end;
  if (!( 1 <= v9 )) goto end;
  goto loc14;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( 1+v16 <= v8 )) goto end;
  v22 = v21;
  v21 = nondet();
  v18 = nondet();
  v9 = 1+v9;
  v10 = 2+v10;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( v8 <= v16 )) goto end;
  goto loc17;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  v7 = 1+v7;
  goto loc15;
 }
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  v21 = 1;
  v18 = 0;
  goto loc19;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v12 = 2-v7+v15;
  goto loc21;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  if (!( v7 <= 1 )) goto end;
  if (!( 1 <= v7 )) goto end;
  v12 = 1;
  goto loc21;
 }
 if (nondet_bool()) {
  if (!( 2 <= v7 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 1 )) goto end;
  goto loc22;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 1+v15 <= v7 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v7 <= v15 )) goto end;
  goto loc23;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1+v16 <= v8 )) goto end;
  v7 = 1+v7;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v8 <= v16 )) goto end;
  v13 = 1+v13;
  v13 = 1+v13;
  v8 = 1+v8;
  goto loc10;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 1+v15 <= v7 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( v7 <= v15 )) goto end;
  goto loc10;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  if (!( 2 <= v11 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 1 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( v11 <= 1 )) goto end;
  if (!( 1 <= v11 )) goto end;
  goto loc3;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  v1 = nondet();
  v2 = nondet();
  v17 = nondet();
  v22 = nondet();
  v20 = nondet();
  v19 = nondet();
  goto loc24;
 }
 goto end;
loc1:
end:
;
}
