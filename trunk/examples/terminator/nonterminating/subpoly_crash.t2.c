int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  v1 = 1+v1;
  v2 = 1+v2;
  goto loc2;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( v2 <= v1 )) goto end;
  if (!( v1 <= v2 )) goto end;
  goto loc0;
 }
 goto end;
loc3:
loc1:
end:
;
}
