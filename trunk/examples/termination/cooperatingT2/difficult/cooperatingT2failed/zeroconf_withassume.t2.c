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
goto loc_24;
loc_24:
 if (nondet_bool()) {
  goto loc_23;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_17;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v9 <= 1+v1 )) goto end;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  v3 = 1;
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v7 = 1+v7;
  if (!( v9 <= 1+v1 )) goto end;
  goto loc_CP_5;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( v9 <= 1+v1 )) goto end;
  goto loc_4;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v6 = -1+v6;
  v8 = 0;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v8 = 1+v8;
  goto loc_6;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  v9 = 1+v9;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc_8;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  v2 = nondet();
  if (!( 0 <= v2 )) goto end;
  if (!( v2 <= 1 )) goto end;
  goto loc_9;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 1+v5 <= 1 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  goto loc_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v6 = -1+v6;
  v8 = 0;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v8 = 1+v8;
  goto loc_11;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  v9 = 1+v9;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc_13;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( 1+v1 <= v7 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( v7 <= v1 )) goto end;
  v5 = nondet();
  if (!( 0 <= v5 )) goto end;
  if (!( v5 <= 1 )) goto end;
  goto loc_14;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  goto loc_15;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v6 = -1+v6;
  v8 = 0;
  goto loc_CP_5;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( v4 <= 0 )) goto end;
  v8 = 1+v8;
  goto loc_CP_5;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  v9 = 1+v9;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  goto loc_CP_5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc_18;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc_CP_5;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc_19;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  goto loc_22;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_21;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_21;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v2 = 0;
  v5 = 0;
  v7 = 0;
  v4 = nondet();
  if (!( 0 <= v4 )) goto end;
  if (!( v4 <= 1 )) goto end;
  goto loc_20;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  v9 = 1;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  v1 = nondet();
  if (!( 0 <= v1 )) goto end;
  v4 = 0;
  v5 = 0;
  v2 = 0;
  v3 = 0;
  v7 = 0;
  goto loc_CP_1;
 }
 goto end;
loc_22:
end:
;
}
