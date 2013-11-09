int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc9;
loc9:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc4;
 }
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  goto loc6;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 0 <= v2 )) goto end;
  goto loc7;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v2 = nondet();
  v1 = 0;
  goto loc1;
 }
 goto end;
loc5:
loc5:
end:
;
}
