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
goto loc_17;
loc_17:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_5;
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
loc_CP_11:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v4 <= v2 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc_CP_4;
 }
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  v2 = 0;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v6 = nondet();
  v7 = nondet();
  goto loc_3;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc_CP_9;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = 1+v2;
  goto loc_CP_11;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v6 = nondet();
  v7 = nondet();
  goto loc_8;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( v4 <= v2 )) goto end;
  v2 = 0;
  goto loc_CP_4;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v4 )) goto end;
  v3 = 0;
  goto loc_CP_9;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc_CP_6;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( 1+v5 <= v2 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v5 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( v2 <= v5 )) goto end;
  if (!( v5 <= v2 )) goto end;
  goto loc_14;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( v4 <= v2 )) goto end;
  v2 = 0;
  goto loc_CP_11;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v4 )) goto end;
  goto loc_15;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  v4 = 5;
  v1 = 10;
  v5 = 0;
  v2 = 0;
  goto loc_CP_6;
 }
 goto end;
loc_1:
end:
;
}
