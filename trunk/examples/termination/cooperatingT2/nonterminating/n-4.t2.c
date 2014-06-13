int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_14;
loc_14:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( 0 <= -1-v3+v4 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( -1*v3+v4 <= 0 )) goto end;
  v1 = nondet();
  goto loc_8;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v2 = nondet();
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v2 = nondet();
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( -1*v4+v5 <= 0 )) goto end;
  v3 = 1+v3;
  goto loc_CP_1;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v2 = nondet();
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v2 = nondet();
  goto loc_12;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc_4;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_2;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v2 = nondet();
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v2 = nondet();
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( -1*v4+v5 <= 0 )) goto end;
  v3 = 1+v3;
  goto loc_CP_1;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_10;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc_CP_2;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  goto loc_CP_3;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_13;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc_CP_2;
 }
 goto end;
loc_8:
end:
;
}
