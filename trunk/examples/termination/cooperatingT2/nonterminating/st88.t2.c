int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
goto loc_13;
loc_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 6 <= v1 )) goto end;
  v2 = nondet();
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 5 )) goto end;
  goto loc_2;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( v1 <= 2 )) goto end;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  v1 = -1+v1;
  goto loc_CP_5;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  goto loc_CP_5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_2;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 6 <= v1 )) goto end;
  v1 = 1+v1;
  goto loc_CP_4;
 }
 if (nondet_bool()) {
  if (!( v1 <= 5 )) goto end;
  v1 = 1+v1;
  goto loc_CP_4;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc_CP_3;
 }
 goto end;
loc_8:
end:
;
}
