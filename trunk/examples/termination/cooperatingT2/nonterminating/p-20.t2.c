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
goto loc_5;
loc_5:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  v5 = v10;
  v6 = -1+v3;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc_2;
 }
 if (nondet_bool()) {
  v5 = v10;
  v6 = -1+v3;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = -1+v3;
  v4 = nondet();
  v9 = v7;
  goto loc_4;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v7 = nondet();
  v10 = nondet();
  v8 = nondet();
  v11 = nondet();
  v9 = v8;
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v5 = v11;
  v6 = v2;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc_2;
 }
 if (nondet_bool()) {
  v5 = v11;
  v6 = v2;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = v3;
  v4 = nondet();
  v9 = v7;
  goto loc_CP_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_3;
 }
 goto end;
loc_2:
end:
;
}
