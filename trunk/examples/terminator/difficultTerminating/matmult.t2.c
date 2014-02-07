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
goto loc_16;
loc_16:
 if (nondet_bool()) {
  goto loc_15;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_8:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_10:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_13:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 20 <= v1 )) goto end;
  v2 = 1+v2;
  goto loc_CP_7;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 20 )) goto end;
  v1 = 1+v1;
  goto loc_CP_8;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 20 <= v2 )) goto end;
  v5 = 1+v5;
  goto loc_CP_10;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 20 )) goto end;
  v1 = 0;
  goto loc_CP_8;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 20 <= v5 )) goto end;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= 20 )) goto end;
  v2 = 0;
  goto loc_CP_7;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( 20 <= v4 )) goto end;
  v7 = 1+v7;
  goto loc_CP_4;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 20 )) goto end;
  v8 = nondet();
  v10 = v8;
  v4 = 1+v4;
  goto loc_CP_13;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 20 <= v7 )) goto end;
  v5 = 0;
  goto loc_CP_10;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 20 )) goto end;
  v4 = 0;
  goto loc_CP_13;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 20 <= v3 )) goto end;
  v6 = 1+v6;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 20 )) goto end;
  v8 = nondet();
  v9 = v8;
  v3 = 1+v3;
  goto loc_CP_2;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 20 <= v6 )) goto end;
  v7 = 0;
  goto loc_CP_4;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= 20 )) goto end;
  v3 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v8 = 0;
  v6 = 0;
  goto loc_CP_0;
 }
 goto end;
loc_12:
end:
;
}
