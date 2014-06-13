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
goto loc_12;
loc_12:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v7 = 0;
  v5 = 1;
  v2 = nondet();
  v9 = v2;
  goto loc_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v4 = nondet();
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v6-v8 <= 1000 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1000 <= v6-v8 )) goto end;
  v10 = 1;
  goto loc_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  v6 = nondet();
  goto loc_8;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_CP_6;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = 0;
  v3 = nondet();
  v8 = v3;
  goto loc_9;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  goto loc_5;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v10 = 1;
  v1 = nondet();
  v7 = v1;
  v10 = 1;
  goto loc_0;
 }
 goto end;
loc_4:
end:
;
}
