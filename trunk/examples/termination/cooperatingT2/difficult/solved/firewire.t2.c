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
goto loc_16;
loc_16:
 if (nondet_bool()) {
  goto loc_15;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v8 <= v7 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v8 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v7 <= v8 )) goto end;
  if (!( v8 <= v7 )) goto end;
  goto loc_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v8 = 1;
  goto loc_CP_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v7 = 1;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v8 = 0;
  goto loc_CP_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v9 = -1+v9;
  v2 = nondet();
  v3 = nondet();
  goto loc_8;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v9 = nondet();
  if (!( 1 <= v9 )) goto end;
  v6 = 1+v6;
  v4 = v6;
  goto loc_8;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1+v5 <= 3 )) goto end;
  v5 = 1+v5;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( 3 <= v5 )) goto end;
  v5 = 0;
  goto loc_9;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v7 = 0;
  goto loc_6;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v2 = v1;
  goto loc_8;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( v1 <= 2 )) goto end;
  v3 = 0;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  v3 = 1;
  v1 = -2+v1;
  goto loc_11;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  v4 = -1+v4;
  v1 = v5;
  goto loc_12;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= 0 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  if (!( 0 <= v9 )) goto end;
  goto loc_13;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v5 = 0;
  v6 = 1;
  v4 = v6;
  v7 = 0;
  v8 = 0;
  v9 = nondet();
  if (!( 1 <= v9 )) goto end;
  goto loc_CP_4;
 }
 goto end;
loc_14:
end:
;
}
