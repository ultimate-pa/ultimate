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
int v8 = nondet();
int v9 = nondet();
int v10 = nondet();
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  v7 = v4;
  v8 = v5;
  if (!( -1*v7+v8 <= 0 )) goto end;
  v7 = nondet();
  v8 = nondet();
  v1 = nondet();
  goto loc_2;
 }
 if (nondet_bool()) {
  v7 = v4;
  v8 = v5;
  if (!( 0 <= -1-v7+v8 )) goto end;
  v7 = nondet();
  v8 = nondet();
  v6 = v4;
  v6 = nondet();
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v10 = nondet();
  v9 = nondet();
  v3 = nondet();
  v2 = nondet();
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_2:
end:
;
}
