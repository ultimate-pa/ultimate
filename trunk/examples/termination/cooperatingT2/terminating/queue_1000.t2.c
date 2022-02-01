int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_18;
loc_18:
 if (nondet_bool()) {
  goto loc_17;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1000 <= v1 )) goto end;
  v1 = 0;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1000 )) goto end;
  v2 = v1;
  goto loc_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc_CP_1;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_4;
 }
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v3 = nondet();
  goto loc_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  goto loc_8;
 }
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1000 <= v1 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1000 )) goto end;
  goto loc_9;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc_CP_6;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  goto loc_13;
 }
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  goto loc_15;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_16;
 }
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_CP_6;
 }
 goto end;
loc_11:
end:
;
}
