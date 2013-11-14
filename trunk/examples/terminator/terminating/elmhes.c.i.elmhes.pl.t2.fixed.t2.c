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
goto loc_23;
loc_23:
 if (nondet_bool()) {
  goto loc_CP_5;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_CP_11:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_CP_19:
 if (nondet_bool()) {
  goto loc_18;
 }
 goto end;
loc_CP_21:
 if (nondet_bool()) {
  goto loc_20;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v5 = nondet();
  v6 = nondet();
  goto loc_2;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc_CP_5;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc_CP_7;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc_CP_9;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc_CP_9;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc_CP_11;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v8 = nondet();
  goto loc_CP_11;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( 0 <= v8 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( 1+v4 <= v1 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v1 <= v4 )) goto end;
  v8 = nondet();
  goto loc_13;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc_CP_7;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 0 )) goto end;
  goto loc_CP_7;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( v4 <= v3 )) goto end;
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v4 )) goto end;
  v7 = 0;
  v1 = v3;
  goto loc_CP_3;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v8 = nondet();
  v2 = 1+v2;
  goto loc_CP_19;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc_CP_19;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v8 = nondet();
  v2 = 1+v2;
  goto loc_CP_21;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  if (!( v3 <= v1 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  goto loc_CP_21;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v3 )) goto end;
  goto loc_CP_21;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc_CP_3;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v5 <= v6 )) goto end;
  goto loc_22;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  v7 = nondet();
  v1 = v2;
  goto loc_22;
 }
 goto end;
loc_17:
end:
;
}
