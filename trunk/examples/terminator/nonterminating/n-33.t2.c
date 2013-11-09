int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc10;
loc10:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( v3 <= 0 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( v3 <= 0 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( v3 <= 0 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v3 = v2;
  v3 = nondet();
  v3 = -1+v3;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v3 = v2;
  v3 = nondet();
  v3 = -1+v3;
  goto loc8;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc9;
 }
 goto end;
loc9:
end:
;
}
