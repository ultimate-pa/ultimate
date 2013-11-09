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
goto loc16;
loc16:
 if (nondet_bool()) {
  goto loc15;
 }
 goto end;
loc0:
 if (nondet_bool()) {
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
loc7:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 20 <= v1 )) goto end;
  v2 = 1+v2;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 20 )) goto end;
  v1 = 1+v1;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 20 <= v2 )) goto end;
  v5 = 1+v5;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 20 )) goto end;
  v1 = 0;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 20 <= v5 )) goto end;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= 20 )) goto end;
  v2 = 0;
  goto loc7;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 20 <= v4 )) goto end;
  v7 = 1+v7;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 20 )) goto end;
  v8 = nondet();
  v10 = v8;
  v4 = 1+v4;
  goto loc13;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 20 <= v7 )) goto end;
  v5 = 0;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 20 )) goto end;
  v4 = 0;
  goto loc13;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 20 <= v3 )) goto end;
  v6 = 1+v6;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 20 )) goto end;
  v8 = nondet();
  v9 = v8;
  v3 = 1+v3;
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 20 <= v6 )) goto end;
  v7 = 0;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= 20 )) goto end;
  v3 = 0;
  goto loc2;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  v8 = 0;
  v6 = 0;
  goto loc0;
 }
 goto end;
loc12:
end:
;
}
