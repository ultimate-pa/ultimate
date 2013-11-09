int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v2 = v2+v3;
  if (!( 0 <= -1-v2 )) goto end;
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  v2 = v2+v3;
  if (!( -1*v2 <= 0 )) goto end;
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
end:
;
}
