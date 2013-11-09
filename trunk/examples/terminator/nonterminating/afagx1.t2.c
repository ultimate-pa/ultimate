int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v2 = 0;
  v2 = 1;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v2 = 1;
  goto loc1;
 }
 goto end;
loc6:
end:
;
}
