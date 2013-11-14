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
goto loc_22;
loc_22:
 if (nondet_bool()) {
  goto loc_21;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_19;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v8 <= 1+v5 )) goto end;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v4 <= v3 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v4 )) goto end;
  v3 = 1+v3;
  goto loc_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v8 = 1+v8;
  v9 = 0;
  v7 = 0;
  v6 = v8;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  goto loc_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v9 = 0;
  v6 = -1+v6;
  goto loc_4;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 2 <= v9 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( v9 <= 1 )) goto end;
  goto loc_5;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  if (!( 1 <= v2 )) goto end;
  v9 = 1+v9;
  goto loc_4;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 2 <= v7 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v7 <= 1 )) goto end;
  goto loc_7;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 1+v2 <= 1 )) goto end;
  v3 = -1+v3;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_2;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v7 = 1+v7;
  goto loc_4;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc_9;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v8 = 1+v8;
  v9 = 0;
  v7 = 0;
  v6 = v8;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  goto loc_12;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  if (!( v1 <= 0 )) goto end;
  v9 = 0;
  v6 = -1+v6;
  goto loc_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( 2 <= v9 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( v9 <= 1 )) goto end;
  goto loc_13;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  if (!( 1 <= v1 )) goto end;
  v9 = 1+v9;
  goto loc_12;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( 2 <= v7 )) goto end;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( v7 <= 1 )) goto end;
  goto loc_15;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v2 = nondet();
  if (!( 0 <= v2 )) goto end;
  if (!( v2 <= 1 )) goto end;
  goto loc_10;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc_16;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( v1 <= 0 )) goto end;
  v7 = 1+v7;
  goto loc_12;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc_17;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  goto loc_20;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  v1 = nondet();
  if (!( 0 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  goto loc_18;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  v8 = 1;
  v9 = 0;
  v6 = v8;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v7 = 0;
  v5 = nondet();
  if (!( 0 <= v5 )) goto end;
  v4 = nondet();
  if (!( 0 <= v4 )) goto end;
  if (!( v4 <= v5 )) goto end;
  v3 = nondet();
  if (!( v3 <= v4 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc_CP_1;
 }
 goto end;
loc_20:
end:
;
}
