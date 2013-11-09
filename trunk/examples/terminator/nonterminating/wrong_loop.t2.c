int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v2 = v1;
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 6 <= v1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 5 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v1 <= 5 )) goto end;
  if (!( 5 <= v1 )) goto end;
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 10 <= v1 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 10 )) goto end;
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v1 = 0;
  goto loc2;
 }
 goto end;
loc5:
end:
;
}
