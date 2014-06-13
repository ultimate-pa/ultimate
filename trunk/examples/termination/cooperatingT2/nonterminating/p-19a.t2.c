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
int v11 = nondet();
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  v4 = v11;
  v5 = v2;
  if (!( v5 <= 0 )) goto end;
  v4 = nondet();
  v5 = nondet();
  v1 = nondet();
  goto loc_1;
 }
 if (nondet_bool()) {
  v4 = v11;
  v5 = v2;
  if (!( 0 <= -1+v5 )) goto end;
  v4 = nondet();
  v5 = nondet();
  v7 = v6;
  v8 = v2;
  v3 = v6;
  v7 = nondet();
  v8 = nondet();
  v3 = nondet();
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
  v9 = nondet();
  v11 = nondet();
  v10 = v9;
  goto loc_CP_0;
 }
 goto end;
loc_1:
end:
;
}
