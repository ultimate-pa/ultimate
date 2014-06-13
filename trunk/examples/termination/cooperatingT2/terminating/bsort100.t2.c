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
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  goto loc_13;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 101 <= v1 )) goto end;
  v3 = 0;
  v7 = 1;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 100 )) goto end;
  v1 = 1+v1;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v7 = 1+v7;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc_CP_9;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = 0;
  goto loc_8;
 }
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( v2 <= 100-v7 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 101-v7 <= v2 )) goto end;
  goto loc_6;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( 100 <= v2 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( v2 <= 99 )) goto end;
  goto loc_12;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 100 <= v7 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( v7 <= 99 )) goto end;
  v3 = 1;
  v2 = 1;
  goto loc_CP_9;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v6 = -1;
  v5 = v6;
  v1 = 1;
  goto loc_CP_2;
 }
 goto end;
loc_4:
end:
;
}
