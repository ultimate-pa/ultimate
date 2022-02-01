int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_2;
loc_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v1 = 0;
  v2 = v1;
  v1 = 1+v1;
  v4 = v1;
  v1 = 1+v1;
  v3 = v1;
  v1 = 1+v1;
  v5 = v1;
  v1 = 1+v1;
  goto loc_1;
 }
 goto end;
loc_1:
end:
;
}
