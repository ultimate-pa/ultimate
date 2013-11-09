int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc9;
loc9:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v4 = nondet();
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  v4 = nondet();
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  if (!( 0 <= -1+v5 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  v4 = nondet();
  goto loc4;
 }
 if (nondet_bool()) {
  v4 = nondet();
  goto loc7;
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
  v2 = v2;
  goto loc5;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v5 = -1+v5;
  if (!( v5 <= 0 )) goto end;
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v3 = v3;
  goto loc8;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v5 = -1+v5;
  if (!( 0 <= -1+v5 )) goto end;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
loc2:
end:
;
}
