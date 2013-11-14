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
loc_CP_0:
 if (nondet_bool()) {
  if (!( 2-v3 <= 0 )) goto end;
  if (!( 0 <= 2-v2 )) goto end;
  v3 = 1+v3;
  v2 = 1+v2;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 2-v3 <= 0 )) goto end;
  if (!( 0 <= 2-v2 )) goto end;
  v3 = 1+v3;
  v2 = 1+v2;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v3 )) goto end;
  v3 = 1+v3;
  v2 = 1+v2;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v3 )) goto end;
  v3 = 1+v3;
  v2 = 1+v2;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v3 )) goto end;
  v3 = 1+v3;
  v2 = 1+v2;
  if (!( v3 <= 2 )) goto end;
  if (!( 2 <= v3 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v3 )) goto end;
  v3 = 1+v3;
  v2 = 1+v2;
  if (!( v3 <= 2 )) goto end;
  if (!( 2 <= v3 )) goto end;
  if (!( v2 <= 2 )) goto end;
  if (!( 2 <= v2 )) goto end;
  v2 = 1;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( 2-v3 <= 0 )) goto end;
  if (!( 3-v2 <= 0 )) goto end;
  v1 = nondet();
  goto loc_16;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1+v3 <= 2 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 3 <= v3 )) goto end;
  goto loc_3;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1+v2 <= 2 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 3 <= v2 )) goto end;
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v3 <= 2 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 3 <= v3 )) goto end;
  goto loc_6;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( v2 <= 2 )) goto end;
  if (!( 2 <= v2 )) goto end;
  v2 = 1;
  goto loc_4;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v3 <= 2 )) goto end;
  goto loc_9;
 }
 if (nondet_bool()) {
  if (!( 3 <= v3 )) goto end;
  goto loc_9;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1+v2 <= 2 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 3 <= v2 )) goto end;
  goto loc_7;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 1+v3 <= 2 )) goto end;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 3 <= v3 )) goto end;
  goto loc_12;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( v2 <= 2 )) goto end;
  if (!( 2 <= v2 )) goto end;
  v2 = 1;
  goto loc_10;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( 1+v2 <= 2 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 3 <= v2 )) goto end;
  goto loc_13;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_16:
end:
;
}
