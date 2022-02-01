int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
int v7 = nondet();
goto loc_18;
loc_18:
 if (nondet_bool()) {
  goto loc_17;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_10:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 100 <= v1 )) goto end;
  v2 = -2+v1;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 100 )) goto end;
  v1 = 1+v1;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v5 = v3;
  v2 = v5;
  goto loc_3;
 }
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v3 = v2;
  goto loc_CP_6;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  goto loc_CP_10;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc_14;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  goto loc_15;
 }
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v6 = v4;
  v2 = v6;
  v7 = nondet();
  goto loc_13;
 }
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  v4 = v2;
  goto loc_CP_10;
 }
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  goto loc_4;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_4:
end:
;
}
