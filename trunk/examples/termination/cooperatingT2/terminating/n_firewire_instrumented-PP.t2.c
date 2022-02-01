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
goto loc_15;
loc_15:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v1 = -1+v1;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  v3 = 1+v3;
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  v4 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( v4 <= 2 )) goto end;
  if (!( v6 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 2 <= v4 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( v4 <= 1 )) goto end;
  if (!( 1 <= v6 )) goto end;
  v4 = 1+v4;
  goto loc_3;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v5 <= v6 )) goto end;
  if (!( v6 <= v5 )) goto end;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v6 )) goto end;
  goto loc_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( v6 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc_3;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v7 = -1+v7;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc_5;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  v3 = 1+v3;
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  v4 = 0;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( v4 <= 2 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc_8;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 2 <= v4 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( v4 <= 1 )) goto end;
  if (!( 1 <= v5 )) goto end;
  v4 = 1+v4;
  goto loc_8;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v6 = nondet();
  if (!( 0 <= v6 )) goto end;
  if (!( v6 <= 1 )) goto end;
  goto loc_6;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc_8;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v7 = -1+v7;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc_11;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = nondet();
  if (!( 0 <= v5 )) goto end;
  if (!( v5 <= 1 )) goto end;
  goto loc_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  v4 = 0;
  v3 = 1;
  v2 = nondet();
  if (!( 1 <= v2 )) goto end;
  v1 = v2;
  v5 = 0;
  v6 = 0;
  goto loc_CP_1;
 }
 goto end;
loc_13:
end:
;
}
