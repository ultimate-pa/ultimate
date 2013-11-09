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
goto loc12;
loc12:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v8 = 0;
  v4 = 1;
  v2 = nondet();
  v10 = v2;
  v13 = v10;
  v16 = v13;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v3 = nondet();
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1+v7-v9 <= 1000 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1000 <= v7-v9 )) goto end;
  v17 = 1;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v17 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v17 <= 0 )) goto end;
  v6 = 0;
  v15 = nondet();
  v11 = v15;
  v7 = v11;
  goto loc8;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v17 <= 0 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1 <= v17 )) goto end;
  v17 = 0;
  v5 = 0;
  v14 = nondet();
  v12 = v14;
  v9 = v12;
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 1 <= v16 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v16 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v17 = 1;
  v1 = nondet();
  v8 = v2;
  v17 = 1;
  goto loc0;
 }
 goto end;
loc4:
end:
;
}
