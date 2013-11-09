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
goto loc17;
loc17:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc15;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc13;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v5 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  v22 = 1;
  v22 = 0;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v5 <= 0 )) goto end;
  v26 = 1;
  v26 = 0;
  goto loc4;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v18 = 0;
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1+v23 <= 2 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 3 <= v23 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 2 <= v23 )) goto end;
  if (!( v23 <= 2 )) goto end;
  v9 = v1;
  v18 = 1+v18;
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v3 = 0;
  goto loc9;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1 <= v23 )) goto end;
  if (!( v23 <= 1 )) goto end;
  v16 = 1+v16;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v23 <= 1 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 2 <= v23 )) goto end;
  goto loc10;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  v10 = v1;
  v11 = v3;
  v25 = nondet();
  v20 = v25;
  v7 = v20;
  v19 = 1;
  v19 = 0;
  v23 = v7;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc7;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( 1+v16 <= v4 )) goto end;
  v8 = v17;
  v12 = v2;
  v13 = v15;
  v14 = v18;
  v24 = nondet();
  v21 = v24;
  v6 = v21;
  v1 = v6;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( v4 <= v16 )) goto end;
  goto loc7;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc12;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  v26 = 0;
  v22 = v26;
  v5 = nondet();
  goto loc0;
 }
 goto end;
loc3:
end:
;
}
