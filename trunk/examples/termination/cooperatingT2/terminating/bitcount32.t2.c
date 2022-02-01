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
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v6 = v6+v10;
  v1 = 1+v1;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v10 = 0;
  goto loc_0;
 }
 if (nondet_bool()) {
  v10 = 1;
  goto loc_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 32 <= v1 )) goto end;
  v7 = v6;
  v9 = v7;
  v4 = v2;
  v5 = v4;
  v5 = nondet();
  v8 = v5;
  v11 = v8;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 32 )) goto end;
  goto loc_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v3 = v2;
  v6 = 0;
  v1 = 0;
  goto loc_CP_1;
 }
 goto end;
loc_4:
end:
;
}
