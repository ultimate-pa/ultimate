int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v1 = 0;
  v2 = 1;
  v3 = nondet();
  goto loc_0;
 }
 goto end;
loc_2:
end:
;
}
