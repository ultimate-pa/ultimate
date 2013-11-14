int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_12;
loc_12:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 100 <= v1 )) goto end;
  v2 = 100;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 100 )) goto end;
  v3 = v1;
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc_CP_3;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 200 <= v2 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 200 )) goto end;
  v5 = v2;
  goto loc_6;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc_CP_5;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v4 = v1;
  goto loc_10;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_CP_5;
 }
 goto end;
loc_8:
end:
;
}
