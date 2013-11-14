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
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  v5 = v2;
  v6 = v3;
  if (!( -1*v5+v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc_2;
 }
 if (nondet_bool()) {
  v5 = v2;
  v6 = v3;
  if (!( 0 <= -1-v5+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = v2;
  v4 = nondet();
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v8 = nondet();
  v7 = nondet();
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
