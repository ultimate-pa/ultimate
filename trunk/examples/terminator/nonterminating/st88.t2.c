int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc13;
loc13:
 if (nondet_bool()) {
  goto loc12;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 6 <= v1 )) goto end;
  v2 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 5 )) goto end;
  goto loc2;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v1 <= 2 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  v1 = -1+v1;
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 6 <= v1 )) goto end;
  v1 = 1+v1;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v1 <= 5 )) goto end;
  v1 = 1+v1;
  goto loc4;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v1 = nondet();
  v1 = nondet();
  goto loc3;
 }
 goto end;
loc8:
end:
;
}
