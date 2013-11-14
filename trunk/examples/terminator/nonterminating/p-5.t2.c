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
goto loc_12;
loc_12:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  if (!( 0 <= v10 )) goto end;
  if (!( 0 <= -1-v12+v13 )) goto end;
  goto loc_0;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  if (!( -1*v11+v12 <= 0 )) goto end;
  v1 = nondet();
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v11+v12 )) goto end;
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v9 = v4;
  if (!( 5-v9 <= 0 )) goto end;
  v9 = nondet();
  v3 = 1;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_1;
 }
 if (nondet_bool()) {
  v9 = v4;
  if (!( 0 <= 4-v9 )) goto end;
  v9 = nondet();
  v8 = v4;
  v8 = nondet();
  v3 = 0;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_CP_2;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 0 <= -1-v12+v13 )) goto end;
  v9 = 0;
  if (!( 0 <= 4-v9 )) goto end;
  v9 = nondet();
  v8 = 0;
  v8 = nondet();
  v3 = 0;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( -1*v12+v13 <= 0 )) goto end;
  v11 = 1+v11;
  goto loc_CP_3;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 1+v10 <= 0 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  goto loc_7;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v12 = 1+v12;
  goto loc_6;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 0 <= -1-v12+v13 )) goto end;
  v9 = 0;
  if (!( 0 <= 4-v9 )) goto end;
  v9 = nondet();
  v8 = 0;
  v8 = nondet();
  v3 = 0;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( -1*v12+v13 <= 0 )) goto end;
  v11 = 1+v11;
  goto loc_CP_3;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v7 = nondet();
  goto loc_CP_3;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v5 = 2;
  v9 = 1;
  if (!( 0 <= 4-v9 )) goto end;
  v9 = nondet();
  v8 = 1;
  v8 = nondet();
  v3 = 0;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_CP_2;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  v6 = 1+v5;
  v9 = v5;
  if (!( 0 <= 4-v9 )) goto end;
  v9 = nondet();
  v8 = v5;
  v8 = nondet();
  v3 = 0;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  v9 = v5;
  if (!( 5-v9 <= 0 )) goto end;
  v9 = nondet();
  v3 = 1;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_1;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v4 = 2;
  v9 = 1;
  if (!( 0 <= 4-v9 )) goto end;
  v9 = nondet();
  v8 = 1;
  v8 = nondet();
  v3 = 0;
  v2 = v3;
  v1 = v2;
  v10 = v1;
  v1 = nondet();
  goto loc_CP_2;
 }
 goto end;
loc_4:
end:
;
}
