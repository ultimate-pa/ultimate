int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+v2 <= v3 )) goto end;
  v3 = 0;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v3 <= v2 )) goto end;
  v3 = 1+v3;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v4 = nondet();
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( v3 <= v1 )) goto end;
  if (!( v1 <= v3 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v3 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  goto loc4;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  if (!( v1 <= v2 )) goto end;
  v3 = 1+v1;
  goto loc1;
 }
 goto end;
loc6:
end:
;
}
