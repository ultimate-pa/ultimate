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
goto loc28;
loc28:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  goto loc17;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v10 <= v9 )) goto end;
  if (!( v9 <= v10 )) goto end;
  v9 = 1+v9;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v10 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v9 )) goto end;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 1+v11 <= v6 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v6 <= v11 )) goto end;
  v6 = 1+v6;
  goto loc5;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1+v6 <= v9 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v9 <= v6 )) goto end;
  goto loc0;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1 <= v13 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= 0 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v13 <= 0 )) goto end;
  if (!( 0 <= v13 )) goto end;
  goto loc6;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 1+v11 <= v8 )) goto end;
  v6 = -1+v6;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( v8 <= v11 )) goto end;
  v4 = nondet();
  v8 = 1+v8;
  goto loc12;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  v14 = nondet();
  v2 = nondet();
  v5 = nondet();
  v13 = nondet();
  v12 = nondet();
  v5 = nondet();
  goto loc12;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( 1 <= v13 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= 0 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( v13 <= 0 )) goto end;
  if (!( 0 <= v13 )) goto end;
  goto loc7;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 1+v6 <= v9 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v9 <= v6 )) goto end;
  v4 = nondet();
  v1 = nondet();
  v13 = nondet();
  goto loc15;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  v5 = nondet();
  v2 = 1;
  v14 = v2;
  v12 = 0;
  goto loc11;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( 1+v5 <= 0 )) goto end;
  v20 = nondet();
  v21 = -1*v20;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( 0 <= v5 )) goto end;
  v19 = nondet();
  v21 = v19;
  goto loc18;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  v5 = nondet();
  v13 = nondet();
  goto loc19;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( 31 <= v18 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 30 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( v18 <= 30 )) goto end;
  if (!( 30 <= v18 )) goto end;
  goto loc20;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v18 = v7;
  v7 = 1+v7;
  goto loc21;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  goto loc24;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  if (!( v10 <= v9 )) goto end;
  if (!( v9 <= v10 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v10 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v9 )) goto end;
  goto loc22;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  v10 = 1+v10;
  goto loc14;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  if (!( 1+v3 <= v3+v17 )) goto end;
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( 1+v3+v17 <= v3 )) goto end;
  goto loc25;
 }
 if (nondet_bool()) {
  if (!( v3+v17 <= v3 )) goto end;
  if (!( v3 <= v3+v17 )) goto end;
  goto loc23;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( v11 <= v10 )) goto end;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( v10 <= -1+v11 )) goto end;
  v15 = nondet();
  v16 = nondet();
  v3 = v15+v16;
  v17 = nondet();
  goto loc26;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1+v11 <= v9 )) goto end;
  goto loc27;
 }
 if (nondet_bool()) {
  if (!( v9 <= v11 )) goto end;
  v7 = 0;
  goto loc2;
 }
 goto end;
loc27:
end:
;
}
