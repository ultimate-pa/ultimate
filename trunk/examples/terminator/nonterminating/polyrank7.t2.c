int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = v1+v2;
  v2 = -2+v2;
  goto loc1;
 }
 if (nondet_bool()) {
  v1 = v1+v3;
  v2 = 1+v2;
  v3 = -2+v3;
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  goto loc0;
 }
 goto end;
end:
;
}
