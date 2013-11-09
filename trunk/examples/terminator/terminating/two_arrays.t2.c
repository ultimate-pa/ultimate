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
goto loc14;
loc14:
 if (nondet_bool()) {
  goto loc13;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
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
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 50 <= v1 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 50 )) goto end;
  v1 = 1+v1;
  goto loc4;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 50 <= v3 )) goto end;
  v1 = 0;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 50 )) goto end;
  v3 = 1+v3;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 50 <= v2 )) goto end;
  v3 = 0;
  v3 = 0;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 50 )) goto end;
  v2 = 1+v2;
  goto loc12;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 50 <= v1 )) goto end;
  v2 = 0;
  v2 = 0;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 50 )) goto end;
  v1 = 1+v1;
  goto loc9;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 50 <= v5 )) goto end;
  v1 = 0;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= 50 )) goto end;
  v5 = 1+v5;
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 50 <= v4 )) goto end;
  v5 = 0;
  v5 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 50 )) goto end;
  v4 = 1+v4;
  goto loc0;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  v1 = 0;
  v6 = nondet();
  v7 = nondet();
  v4 = 0;
  v4 = 0;
  goto loc0;
 }
 goto end;
loc3:
end:
;
}
