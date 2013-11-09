int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v3 = nondet();
  v2 = -1+v2;
  goto loc2;
 }
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 11 <= v1 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v1 <= 10 )) goto end;
  v2 = v1;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v1 = 2;
  goto loc0;
 }
 goto end;
loc4:
end:
;
}
