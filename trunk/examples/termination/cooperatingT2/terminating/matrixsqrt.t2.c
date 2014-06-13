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
goto loc_21;
loc_21:
 if (nondet_bool()) {
  goto loc_20;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_13:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_CP_17:
 if (nondet_bool()) {
  goto loc_19;
 }
 goto end;
loc_CP_18:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v7 = 1;
  goto loc_5;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v7 = 1;
  goto loc_5;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v7 = 1;
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v7 = 1;
  goto loc_5;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_8;
 }
 if (nondet_bool()) {
  v7 = 0;
  goto loc_5;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  goto loc_7;
 }
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  goto loc_6;
 }
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  goto loc_4;
 }
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( v1 <= v4 )) goto end;
  v3 = 1+v3;
  goto loc_CP_17;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v1 )) goto end;
  v4 = 1+v4;
  goto loc_CP_18;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = 1+v2;
  goto loc_CP_13;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v4 = 0;
  goto loc_CP_18;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v3 = 0;
  goto loc_CP_17;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = 1+v2;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v3 = 1+v3;
  goto loc_CP_2;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  v2 = 0;
  goto loc_CP_13;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v3 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  v1 = 2;
  v5 = nondet();
  v6 = nondet();
  v2 = 0;
  goto loc_CP_0;
 }
 goto end;
loc_9:
end:
;
}
