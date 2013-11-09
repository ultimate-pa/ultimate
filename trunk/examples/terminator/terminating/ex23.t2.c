int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 36 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 36 )) goto end;
  v3 = 1+v3;
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v2 <= 127 )) goto end;
  v3 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 128 <= v2 )) goto end;
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v1 = 0;
  goto loc3;
 }
 goto end;
loc1:
loc1:
end:
;
}
