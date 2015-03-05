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
int v8 = nondet();
int v9 = nondet();
int v10 = nondet();
goto loc_18;
loc_18:
 if (nondet_bool()) {
  goto loc_17;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_CP_12:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_13:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_CP_16:
 if (nondet_bool()) {
  goto loc_15;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v2 = 1+v2;
  goto loc_CP_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( v1 <= v6 )) goto end;
  v2 = 0;
  goto loc_CP_4;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v1 )) goto end;
  v6 = 1+v6;
  goto loc_CP_8;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( v1 <= v5 )) goto end;
  v6 = 0;
  goto loc_CP_8;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v1 )) goto end;
  v5 = 1+v5;
  goto loc_CP_12;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( v1 <= v4 )) goto end;
  v5 = 0;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v1 )) goto end;
  v4 = 1+v4;
  goto loc_CP_16;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  v4 = 0;
  goto loc_CP_16;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v2 = 1+v2;
  goto loc_CP_13;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = 0;
  goto loc_CP_13;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v3 = 1+v3;
  goto loc_CP_9;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( v1 <= v8 )) goto end;
  v3 = 0;
  goto loc_CP_9;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v1 )) goto end;
  v8 = 1+v8;
  goto loc_CP_5;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v1 <= v7 )) goto end;
  v8 = 0;
  goto loc_CP_5;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v1 )) goto end;
  v7 = 1+v7;
  goto loc_CP_0;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  v2 = 0;
  v9 = nondet();
  v10 = nondet();
  v7 = 0;
  goto loc_CP_0;
 }
 goto end;
loc_3:
end:
;
}
