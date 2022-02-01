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
int v18 = nondet();
int v19 = nondet();
int v20 = nondet();
int v21 = nondet();
int v22 = nondet();
int v23 = nondet();
goto loc_13;
loc_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_8:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v15 = 0;
  v23 = 1;
  v23 = 0;
  goto loc_CP_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v20 <= 2 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 3 <= v20 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 2 <= v20 )) goto end;
  if (!( v20 <= 2 )) goto end;
  v6 = v1;
  v15 = 1+v15;
  goto loc_4;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v3 = 0;
  goto loc_5;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 1 <= v20 )) goto end;
  if (!( v20 <= 1 )) goto end;
  v13 = 1+v13;
  goto loc_CP_8;
 }
 if (nondet_bool()) {
  if (!( 1+v20 <= 1 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 2 <= v20 )) goto end;
  goto loc_6;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  v7 = v1;
  v8 = v3;
  v22 = nondet();
  v17 = v22;
  v20 = v17;
  v16 = 1;
  v16 = 0;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_2;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  goto loc_CP_3;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1+v13 <= v4 )) goto end;
  v5 = v14;
  v9 = v2;
  v10 = v12;
  v11 = v15;
  v21 = nondet();
  v18 = v21;
  v1 = v18;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( v4 <= v13 )) goto end;
  goto loc_2;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v23 = 0;
  v19 = v23;
  v19 = 1;
  v19 = 0;
  goto loc_CP_8;
 }
 goto end;
loc_1:
end:
;
}
