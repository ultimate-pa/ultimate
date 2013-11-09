int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v2 = nondet();
  goto loc3;
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
  if (!( 5 <= v1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 4 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v1 <= 4 )) goto end;
  if (!( 4 <= v1 )) goto end;
  v1 = 0;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc4;
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
loc5:
 if (nondet_bool()) {
  v1 = 0;
  goto loc1;
 }
 goto end;
loc4:
end:
;
}
