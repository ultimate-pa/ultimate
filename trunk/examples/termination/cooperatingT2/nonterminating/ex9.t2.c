int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc_13;
loc_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  goto loc_CP_7;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  goto loc_6;
 }
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v5 = nondet();
  goto loc_CP_9;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_11;
 }
 if (nondet_bool()) {
  goto loc_CP_7;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( v2 <= v1 )) goto end;
  goto loc_CP_9;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v2 )) goto end;
  v6 = nondet();
  v1 = 1+v1;
  goto loc_CP_4;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = v4;
  v2 = v3;
  v1 = 0;
  goto loc_CP_4;
 }
 goto end;
loc_3:
end:
;
}
