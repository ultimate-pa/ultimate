int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc_12;
loc_12:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  v3 = nondet();
  v4 = v3;
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v1 = nondet();
  goto loc_3;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v4 = v3;
  goto loc_8;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v2 = nondet();
  v5 = v2;
  v6 = v5;
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v3 = nondet();
  v4 = v3;
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v1 = nondet();
  goto loc_3;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v4 = v3;
  goto loc_5;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 0 <= -1+v6 )) goto end;
  v6 = 1+v6;
  goto loc_CP_4;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_9;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 0 <= -1+v6 )) goto end;
  v6 = 1+v6;
  goto loc_7;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v3 = nondet();
  v4 = v3;
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  v1 = nondet();
  goto loc_3;
 }
 if (nondet_bool()) {
  v3 = nondet();
  v4 = v3;
  goto loc_10;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_11;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 0 <= -1+v6 )) goto end;
  v6 = 1+v6;
  goto loc_CP_4;
 }
 goto end;
loc_3:
end:
;
}
