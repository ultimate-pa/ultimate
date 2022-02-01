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
goto loc_11;
loc_11:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  if (!( 0 <= v7 )) goto end;
  if (!( 0 <= -2-v6+v8 )) goto end;
  v14 = nondet();
  v12 = v14;
  v5 = v12;
  v6 = 1+v6;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 0 <= v7 )) goto end;
  if (!( -1-v6+v8 <= 0 )) goto end;
  v2 = v5;
  v1 = v2;
  if (!( 0 <= v7 )) goto end;
  v13 = v1;
  v1 = nondet();
  if (!( 0 <= v7 )) goto end;
  v15 = v4;
  if (!( 0 <= v7 )) goto end;
  goto loc_6;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  if (!( v15 <= 0 )) goto end;
  if (!( 0 <= v15 )) goto end;
  v1 = nondet();
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  goto loc_9;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v9 = nondet();
  v5 = 0;
  v6 = 0;
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 0 <= -2-v6+v8 )) goto end;
  v14 = nondet();
  v12 = v14;
  v5 = v12;
  v6 = 1+v6;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( -1-v6+v8 <= 0 )) goto end;
  v2 = v5;
  v1 = v2;
  v13 = v1;
  v1 = nondet();
  v15 = v4;
  if (!( v15 <= 0 )) goto end;
  if (!( 0 <= v15 )) goto end;
  v1 = nondet();
  goto loc_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_2;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1+v15 <= 0 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  goto loc_7;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v11 = v15;
  v10 = nondet();
  v15 = v10;
  v10 = nondet();
  goto loc_CP_5;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1+v15 <= 0 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  goto loc_10;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  v11 = v15;
  v10 = nondet();
  v15 = v10;
  v10 = nondet();
  goto loc_8;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  goto loc_CP_5;
 }
 goto end;
loc_3:
end:
;
}
