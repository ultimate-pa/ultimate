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
int v11 = nondet();
goto loc_32;
loc_32:
 if (nondet_bool()) {
  goto loc_29;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_27;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_13:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_16:
 if (nondet_bool()) {
  goto loc_21;
 }
 goto end;
loc_CP_20:
 if (nondet_bool()) {
  goto loc_19;
 }
 goto end;
loc_CP_22:
 if (nondet_bool()) {
  goto loc_18;
 }
 goto end;
loc_CP_24:
 if (nondet_bool()) {
  goto loc_26;
 }
 goto end;
loc_CP_25:
 if (nondet_bool()) {
  goto loc_23;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  v10 = nondet();
  v9 = v10;
  goto loc_2;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc_CP_5;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1+v7 <= v3 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v3 <= v7 )) goto end;
  v3 = 1+v3;
  goto loc_CP_7;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v2 = nondet();
  goto loc_CP_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  if (!( v7 <= v5 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v7 )) goto end;
  goto loc_8;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  goto loc_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 1+v7 <= v6 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( v6 <= v7 )) goto end;
  v2 = nondet();
  v6 = 1+v6;
  goto loc_CP_13;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( v5 <= v4 )) goto end;
  if (!( v4 <= v5 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v5 )) goto end;
  goto loc_CP_13;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v4 )) goto end;
  goto loc_CP_13;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc_CP_16;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  v1 = v2;
  v4 = v3;
  goto loc_15;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  if (!( 1+v7 <= v3 )) goto end;
  goto loc_CP_5;
 }
 if (nondet_bool()) {
  if (!( v3 <= v7 )) goto end;
  v1 = 0;
  goto loc_CP_3;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( v5 <= v6 )) goto end;
  v11 = nondet();
  v2 = nondet();
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  v8 = nondet();
  v6 = 1+v6;
  goto loc_CP_20;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  if (!( 1+v7 <= v3 )) goto end;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( v3 <= v7 )) goto end;
  v8 = nondet();
  goto loc_CP_20;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  if (!( v3 <= v6 )) goto end;
  v3 = 1+v3;
  goto loc_CP_24;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v3 )) goto end;
  v8 = nondet();
  v6 = 1+v6;
  goto loc_CP_25;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  if (!( v5 <= v3 )) goto end;
  v1 = 0;
  goto loc_CP_16;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v5 )) goto end;
  v8 = nondet();
  goto loc_CP_25;
 }
 goto end;
loc_27:
 if (nondet_bool()) {
  if (!( 1+v7 <= v5 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  if (!( v5 <= v7 )) goto end;
  goto loc_CP_24;
 }
 goto end;
loc_29:
 if (nondet_bool()) {
  goto loc_CP_22;
 }
 goto end;
loc_30:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc_CP_22;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_30;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  goto loc_30;
 }
 goto end;
loc_31:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc_CP_3;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v9 <= v1 )) goto end;
  goto loc_31;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v9 )) goto end;
  v1 = v9;
  goto loc_31;
 }
 goto end;
loc_28:
end:
;
}
