int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
int v7 = nondet();
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  v3 = v6;
  v1 = v3;
  goto loc_4;
 }
 if (nondet_bool()) {
  v2 = v7;
  v1 = v2;
  v6 = v1;
  v1 = nondet();
  goto loc_1;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v2 = v7;
  v1 = v2;
  v6 = v1;
  v1 = nondet();
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v2 = v7;
  v1 = v2;
  v6 = v1;
  v1 = nondet();
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc_CP_3;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v4 = 4;
  v5 = 0;
  v6 = 0;
  goto loc_CP_3;
 }
 goto end;
loc_4:
end:
;
}
