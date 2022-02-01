int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_13;
loc_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  v3 = nondet();
  goto loc_2;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  v1 = -1+v1;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( v1 <= 2 )) goto end;
  goto loc_CP_0;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 6 <= v1 )) goto end;
  v1 = 1+v1;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 5 )) goto end;
  v1 = 1+v1;
  goto loc_CP_1;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_CP_3;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 6 <= v1 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( v1 <= 5 )) goto end;
  goto loc_11;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v1 = nondet();
  v2 = nondet();
  v1 = v2;
  goto loc_CP_0;
 }
 goto end;
loc_6:
end:
;
}
