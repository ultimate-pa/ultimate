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
  if (!( v6 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  v6 = 0;
  v2 = 1;
  v1 = nondet();
  v8 = v1;
  v11 = v8;
  v14 = v11;
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
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1+v5-v7 <= 1000 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1000 <= v5-v7 )) goto end;
  v15 = 1;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v15 <= 0 )) goto end;
  v4 = 0;
  v13 = nondet();
  v9 = v13;
  v5 = v9;
  goto loc8;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v15 <= 0 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  v15 = 0;
  v3 = 0;
  v12 = nondet();
  v10 = v12;
  v7 = v10;
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
  if (!( 1 <= v14 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v14 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v15 = 1;
  v6 = nondet();
  v15 = 1;
  goto loc0;
 }
 goto end;
loc4:
end:
;
}
