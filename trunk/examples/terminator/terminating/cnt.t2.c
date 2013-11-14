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
int v12 = nondet();
int v13 = nondet();
int v14 = nondet();
int v15 = nondet();
int v16 = nondet();
int v17 = nondet();
goto loc_12;
loc_12:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_8:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc_CP_3;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v12 = nondet();
  v9 = 1+v9;
  goto loc_2;
 }
 if (nondet_bool()) {
  v6 = nondet();
  v3 = 1+v3;
  goto loc_2;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 10 <= v1 )) goto end;
  v7 = 1+v7;
  goto loc_CP_8;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 10 )) goto end;
  goto loc_6;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 10 <= v7 )) goto end;
  v11 = v12;
  v10 = v9;
  v5 = v6;
  v4 = v3;
  v15 = 1500;
  v16 = nondet();
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 10 )) goto end;
  v1 = 0;
  goto loc_CP_3;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 10 <= v2 )) goto end;
  v8 = 1+v8;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 10 )) goto end;
  v13 = nondet();
  v17 = v13;
  v2 = 1+v2;
  goto loc_CP_4;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 10 <= v8 )) goto end;
  v14 = 1000;
  v12 = 0;
  v6 = 0;
  v9 = 0;
  v3 = 0;
  v7 = 0;
  goto loc_CP_8;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 10 )) goto end;
  v2 = 0;
  goto loc_CP_4;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v13 = 0;
  v8 = 0;
  goto loc_CP_0;
 }
 goto end;
loc_10:
end:
;
}
