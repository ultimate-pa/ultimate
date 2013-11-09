int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v2 = 2+v2;
  v1 = 2+v2;
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 20 <= v2 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 20 )) goto end;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v2 = 0;
  goto loc2;
 }
 goto end;
loc1:
end:
;
}
