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
  goto loc_3;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  v5 = v8;
  v3 = v2;
  if (!( v3 <= 0 )) goto end;
  v5 = nondet();
  v3 = nondet();
  v1 = nondet();
  goto loc_1;
 }
 if (nondet_bool()) {
  v5 = v8;
  v3 = v2;
  if (!( 0 <= -1+v3 )) goto end;
  v5 = nondet();
  v3 = nondet();
  v4 = v2;
  v4 = nondet();
  goto loc_2;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v6 = nondet();
  v8 = nondet();
  v7 = v6;
  goto loc_CP_0;
 }
 goto end;
loc_1:
end:
;
}
