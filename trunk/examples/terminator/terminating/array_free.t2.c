int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc4;
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
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc2;
 }
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 42 <= v1 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 42 )) goto end;
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v1 = 0;
  goto loc1;
 }
 goto end;
loc5:
end:
;
}
