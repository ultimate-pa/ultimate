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
goto loc_13;
loc_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v8 = v2;
  v14 = v8;
  v18 = nondet();
  goto loc_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 1+v17 <= v16 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( v16 <= v17 )) goto end;
  v12 = nondet();
  goto loc_3;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1+v6 <= v2 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( v2 <= v6 )) goto end;
  v13 = nondet();
  goto loc_2;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v11 = nondet();
  goto loc_6;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v5 <= v3 )) goto end;
  v7 = v5;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( v3 <= v5 )) goto end;
  v7 = v3;
  goto loc_9;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v9 = v7;
  v10 = v9;
  v16 = v10+v16;
  goto loc_3;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1+v5 <= v1 )) goto end;
  v7 = v5;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( v1 <= v5 )) goto end;
  v7 = v1;
  goto loc_9;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  goto loc_10;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v18 <= v16 )) goto end;
  v2 = v18;
  v4 = v17;
  v6 = v16;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( v16 <= v18 )) goto end;
  v1 = v16;
  v3 = v17;
  v5 = v18;
  goto loc_11;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1+v18 <= v17 )) goto end;
  v15 = v17-v18;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( v17 <= v18 )) goto end;
  v15 = v17+v18;
  goto loc_0;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v16 = 10;
  v17 = 2;
  v18 = 1;
  goto loc_4;
 }
 goto end;
loc_1:
end:
;
}
