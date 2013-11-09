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
goto loc11;
loc11:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v6 = v1;
  v2 = nondet();
  v4 = v2;
  goto loc0;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc7;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( v5 <= 0 )) goto end;
  if (!( 0 <= v5 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= 0 )) goto end;
  goto loc6;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 10 <= v1 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 10 )) goto end;
  v7 = v1;
  v3 = nondet();
  v5 = v3;
  goto loc8;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v1 = 0;
  goto loc7;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 10 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 10 )) goto end;
  v1 = 1+v1;
  goto loc3;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v1 = 0;
  goto loc3;
 }
 goto end;
loc5:
end:
;
}
