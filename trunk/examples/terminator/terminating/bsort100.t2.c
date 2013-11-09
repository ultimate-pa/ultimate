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
goto loc15;
loc15:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc13;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 101 <= v1 )) goto end;
  v3 = 0;
  v7 = 1;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 100 )) goto end;
  v1 = 1+v1;
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
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v7 = 1+v7;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc9;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = 0;
  goto loc8;
 }
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( v2 <= 100-v7 )) goto end;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 101-v7 <= v2 )) goto end;
  goto loc6;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( 100 <= v2 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( v2 <= 99 )) goto end;
  goto loc12;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 100 <= v7 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v7 <= 99 )) goto end;
  v3 = 1;
  v2 = 1;
  goto loc9;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v6 = -1;
  v5 = v6;
  v1 = 1;
  goto loc2;
 }
 goto end;
loc4:
end:
;
}
