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
int v23 = nondet();
int v24 = nondet();
int v25 = nondet();
int v26 = nondet();
goto loc22;
loc22:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc12;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v5 = v14;
  v8 = v21;
  v23 = nondet();
  v19 = v23;
  v26 = v19;
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc19;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v17 = 1+v17;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v12 = nondet();
  v11 = 0;
  v10 = nondet();
  goto loc4;
 }
 if (nondet_bool()) {
  v6 = nondet();
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 1+v13 <= v16 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v16 <= v13 )) goto end;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( v26 <= 0 )) goto end;
  if (!( 0 <= v26 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v26 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v26 <= 0 )) goto end;
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( 1+v2 <= v17 )) goto end;
  v4 = 1;
  v4 = 0;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( v17 <= v2 )) goto end;
  v25 = nondet();
  goto loc9;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  goto loc15;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  v1 = 1;
  v1 = 0;
  v17 = 1;
  goto loc5;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  v17 = 1+v17;
  goto loc2;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( 1+v13 <= v16 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( v16 <= v13 )) goto end;
  v12 = nondet();
  v11 = 0;
  v15 = 1;
  goto loc16;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( v22 <= 0 )) goto end;
  if (!( 0 <= v22 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1 <= v22 )) goto end;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v22 <= 0 )) goto end;
  goto loc17;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  goto loc13;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v3 <= v17 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 1+v17 <= v3 )) goto end;
  v7 = v14;
  v9 = v21;
  v24 = nondet();
  v20 = v24;
  v22 = v20;
  goto loc18;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( 2 <= v18 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 1 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( v18 <= 1 )) goto end;
  if (!( 1 <= v18 )) goto end;
  v17 = 0;
  goto loc2;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  v18 = nondet();
  v4 = 0;
  v1 = v4;
  v3 = nondet();
  v2 = nondet();
  goto loc20;
 }
 goto end;
loc1:
end:
;
}
