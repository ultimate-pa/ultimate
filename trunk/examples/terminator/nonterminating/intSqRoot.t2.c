int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v4 = v2;
  goto loc1;
 }
 if (nondet_bool()) {
  v3 = v2;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v3 <= 1+v4 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 2+v4 <= v3 )) goto end;
  v2 = nondet();
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v4 = 1;
  v3 = v1;
  goto loc1;
 }
 goto end;
loc3:
end:
;
}
