int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 20 <= v1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 20 )) goto end;
  v1 = 1+v1;
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v1 = 0;
  v1 = nondet();
  goto loc4;
 }
 goto end;
loc1:
end:
;
}
