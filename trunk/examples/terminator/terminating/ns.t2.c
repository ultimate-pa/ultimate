int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_13;
loc_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 5 <= v1 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 5 )) goto end;
  v2 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc_CP_9;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  goto loc_8;
 }
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 5 <= v4 )) goto end;
  v3 = 1+v3;
  goto loc_CP_6;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 5 )) goto end;
  goto loc_11;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 5 <= v3 )) goto end;
  v2 = 1+v2;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 5 )) goto end;
  v4 = 0;
  goto loc_CP_9;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 5 <= v2 )) goto end;
  v1 = 1+v1;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 5 )) goto end;
  v3 = 0;
  goto loc_CP_6;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v5 = 400;
  v1 = 0;
  goto loc_CP_3;
 }
 goto end;
loc_5:
end:
;
}
