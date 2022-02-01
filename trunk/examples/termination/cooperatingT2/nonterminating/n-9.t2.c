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
goto loc_7;
loc_7:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( v9 <= v1 )) goto end;
  v1 = nondet();
  v5 = v7;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v9 )) goto end;
  v1 = nondet();
  v3 = nondet();
  v6 = v3;
  v3 = nondet();
  if (!( 0 <= v6 )) goto end;
  if (!( v6 <= 0 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v9 )) goto end;
  v1 = nondet();
  v3 = nondet();
  v6 = v3;
  v3 = nondet();
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v4 = v8;
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= 0 )) goto end;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v2 = nondet();
  goto loc_4;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_2:
end:
;
}
