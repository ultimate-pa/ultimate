int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc9;
loc9:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 30 <= v2 )) goto end;
  v6 = 1;
  v3 = v6;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 30 )) goto end;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 13 <= v5 )) goto end;
  v2 = 1+v2;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v5 <= 12 )) goto end;
  v2 = 10+v2;
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1+v5 <= 10 )) goto end;
  v2 = 1+v2;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 10 <= v5 )) goto end;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( v5 <= 5 )) goto end;
  v5 = 2+v5;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 6 <= v5 )) goto end;
  v5 = nondet();
  goto loc6;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v2 <= v5 )) goto end;
  v2 = 2+v2;
  v5 = -10+v5;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v2 )) goto end;
  goto loc7;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v1 = 1;
  v4 = 1;
  v3 = 0;
  v2 = v1;
  v5 = v4;
  goto loc3;
 }
 goto end;
loc1:
end:
;
}
