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
goto loc_27;
loc_27:
 if (nondet_bool()) {
  goto loc_26;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  goto loc_21;
 }
 goto end;
loc_CP_8:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_18:
 if (nondet_bool()) {
  goto loc_19;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v10 = 0;
  goto loc_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v10 = 1;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_2;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v10 = 1;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_3;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc_CP_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v2 = v9;
  goto loc_5;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  v9 = 1;
  goto loc_7;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v9 = 0;
  goto loc_7;
 }
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v9 = 0;
  goto loc_7;
 }
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v9 = 0;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v2 = v8;
  goto loc_13;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v8 = 1;
  goto loc_14;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  goto loc_15;
 }
 if (nondet_bool()) {
  v8 = 0;
  goto loc_14;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  v8 = 0;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc_16;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc_16;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  if (!( v4 <= v5 )) goto end;
  if (!( v5 <= v4 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v5 )) goto end;
  goto loc_17;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  if (!( v3 <= v5 )) goto end;
  v4 = 1+v4;
  goto loc_CP_18;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v3 )) goto end;
  goto loc_20;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  v1 = v7;
  v5 = 0;
  goto loc_CP_6;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  v7 = 1;
  goto loc_22;
 }
 if (nondet_bool()) {
  v7 = 0;
  goto loc_22;
 }
 goto end;
loc_24:
 if (nondet_bool()) {
  v7 = 0;
  goto loc_22;
 }
 if (nondet_bool()) {
  goto loc_23;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v7 = 0;
  goto loc_22;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_24;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_24;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( v3 <= v4 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v3 )) goto end;
  goto loc_25;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( v3 <= v4 )) goto end;
  v4 = 0;
  goto loc_CP_18;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v3 )) goto end;
  v4 = 1+v4;
  goto loc_CP_8;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  v3 = 9;
  v1 = 1;
  v2 = 1;
  v6 = nondet();
  v4 = 0;
  goto loc_CP_8;
 }
 goto end;
loc_1:
end:
;
}
