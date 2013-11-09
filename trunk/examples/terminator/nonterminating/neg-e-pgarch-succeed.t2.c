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
  if (!( v7 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v7 = 0;
  v5 = 1;
  v2 = nondet();
  v9 = v2;
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
  v4 = nondet();
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1+v6-v8 <= 1000 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1000 <= v6-v8 )) goto end;
  v10 = 1;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  v6 = nondet();
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = 0;
  v3 = nondet();
  v8 = v3;
  goto loc9;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v10 = 1;
  v1 = nondet();
  v7 = v1;
  v10 = 1;
  goto loc0;
 }
 goto end;
loc4:
end:
;
}
