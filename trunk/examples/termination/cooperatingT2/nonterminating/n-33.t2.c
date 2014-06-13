int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_10;
loc_10:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( v3 <= 0 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( v3 <= 0 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( v3 <= 0 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v3 = v2;
  v3 = nondet();
  v3 = -1+v3;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( -1*v3 <= 0 )) goto end;
  if (!( 0 <= -1+v3 )) goto end;
  v3 = nondet();
  v3 = 1+v3;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3 )) goto end;
  v3 = nondet();
  v3 = -1+v3;
  if (!( 0 <= -1-v3 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v3 = v2;
  v3 = nondet();
  v3 = -1+v3;
  goto loc_8;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc_9;
 }
 goto end;
loc_9:
end:
;
}
