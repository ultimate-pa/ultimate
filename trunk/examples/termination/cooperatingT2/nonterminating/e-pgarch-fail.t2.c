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
  if (!( v6 <= 0 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  v6 = 0;
  v2 = 1;
  v1 = nondet();
  v8 = v1;
  v11 = v8;
  v14 = v11;
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
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v5-v7 <= 1000 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1000 <= v5-v7 )) goto end;
  v15 = 1;
  goto loc_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( v15 <= 0 )) goto end;
  v4 = 0;
  v13 = nondet();
  v9 = v13;
  v5 = v9;
  goto loc_8;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v15 <= 0 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  v15 = 0;
  v3 = 0;
  v12 = nondet();
  v10 = v12;
  v7 = v10;
  goto loc_9;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_CP_6;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1 <= v14 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v14 <= 0 )) goto end;
  goto loc_5;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v15 = 1;
  v6 = nondet();
  v15 = 1;
  goto loc_0;
 }
 goto end;
loc_4:
end:
;
}
