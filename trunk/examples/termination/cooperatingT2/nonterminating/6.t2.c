int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc_5;
loc_5:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  v1 = 3;
  v1 = 2;
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v1 = 2;
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_2;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v1 = 2;
  goto loc_CP_2;
 }
 goto end;
end:
;
}
