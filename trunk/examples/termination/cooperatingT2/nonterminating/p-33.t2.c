int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc_8;
loc_8:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( -1*v2 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( -1*v2 <= 0 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v2 = nondet();
  v2 = 1+v2;
  if (!( -1*v2 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v2 )) goto end;
  v2 = nondet();
  v2 = -1+v2;
  if (!( -1*v2 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( -1*v2 <= 0 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v2 = nondet();
  v2 = 1+v2;
  if (!( -1*v2 <= 0 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v2 = nondet();
  v2 = 1+v2;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( -1*v2 <= 0 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v2 = nondet();
  v2 = 1+v2;
  if (!( 0 <= -1-v2 )) goto end;
  v2 = nondet();
  v2 = -1+v2;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v2 )) goto end;
  v2 = nondet();
  v2 = -1+v2;
  if (!( -1*v2 <= 0 )) goto end;
  if (!( 0 <= -1+v2 )) goto end;
  v2 = nondet();
  v2 = 1+v2;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v2 )) goto end;
  v2 = nondet();
  v2 = -1+v2;
  if (!( 0 <= -1-v2 )) goto end;
  v2 = nondet();
  v2 = -1+v2;
  goto loc_6;
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
loc_2:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc_7;
 }
 goto end;
loc_7:
end:
;
}
