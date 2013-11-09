int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v1 = 3;
  v1 = 2;
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = 2;
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v1 = 2;
  goto loc2;
 }
 goto end;
end:
;
}
