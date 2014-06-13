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
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  v4 = v2;
  if (!( -1*v4+v7 <= 0 )) goto end;
  v4 = nondet();
  v1 = nondet();
  goto loc_2;
 }
 if (nondet_bool()) {
  v4 = v2;
  if (!( 0 <= -1-v4+v7 )) goto end;
  v4 = nondet();
  v3 = v2;
  v3 = nondet();
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v6 = nondet();
  v5 = v6;
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
