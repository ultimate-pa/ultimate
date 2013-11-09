int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 20-v2 <= 0 )) goto end;
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= 19-v2 )) goto end;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 30-v3 <= 0 )) goto end;
  v2 = -1+v2;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 0 <= 29-v3 )) goto end;
  v2 = -1+v2;
  goto loc4;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc1:
end:
;
}
