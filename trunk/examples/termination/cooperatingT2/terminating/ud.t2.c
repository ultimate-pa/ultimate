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
int v12 = nondet();
int v13 = nondet();
goto loc_29;
loc_29:
 if (nondet_bool()) {
  goto loc_28;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_CP_7:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_CP_10:
 if (nondet_bool()) {
  goto loc_14;
 }
 goto end;
loc_CP_11:
 if (nondet_bool()) {
  goto loc_9;
 }
 goto end;
loc_CP_12:
 if (nondet_bool()) {
  goto loc_13;
 }
 goto end;
loc_CP_15:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_CP_17:
 if (nondet_bool()) {
  goto loc_21;
 }
 goto end;
loc_CP_23:
 if (nondet_bool()) {
  goto loc_25;
 }
 goto end;
loc_CP_26:
 if (nondet_bool()) {
  goto loc_27;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  v3 = -1+v3;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( v5 <= v8 )) goto end;
  v13 = nondet();
  v5 = 1+v5;
  goto loc_CP_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  v11 = 0;
  v1 = v11;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  v13 = nondet();
  v5 = 1+v3;
  goto loc_CP_4;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  if (!( v3 <= v5 )) goto end;
  v3 = 1+v3;
  goto loc_CP_10;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v3 )) goto end;
  v13 = nondet();
  v5 = 1+v5;
  goto loc_CP_11;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( 1+v8 <= v3 )) goto end;
  v3 = -1+v8;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( v3 <= v8 )) goto end;
  v13 = nondet();
  v5 = 0;
  goto loc_CP_11;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( 1+v3 <= v6 )) goto end;
  v5 = 1+v5;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  if (!( v6 <= v3 )) goto end;
  v13 = nondet();
  v6 = 1+v6;
  goto loc_CP_15;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  v3 = 1+v3;
  goto loc_CP_17;
 }
 if (nondet_bool()) {
  if (!( v5 <= v8 )) goto end;
  v13 = nondet();
  v6 = 0;
  goto loc_CP_15;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc_CP_0;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( v3 <= v6 )) goto end;
  goto loc_18;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v3 )) goto end;
  v13 = nondet();
  v6 = 1+v6;
  goto loc_CP_7;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  v6 = 0;
  goto loc_CP_7;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc_18;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_19;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_19;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 1+v8 <= v5 )) goto end;
  v5 = 1+v3;
  goto loc_CP_12;
 }
 if (nondet_bool()) {
  if (!( v5 <= v8 )) goto end;
  v13 = nondet();
  goto loc_20;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  if (!( v8 <= v3 )) goto end;
  v3 = 1;
  goto loc_CP_10;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v8 )) goto end;
  v5 = 1+v3;
  goto loc_CP_0;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  v12 = nondet();
  v4 = 1+v4;
  goto loc_CP_23;
 }
 goto end;
loc_24:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc_22;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v4 )) goto end;
  goto loc_22;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  if (!( v4 <= v2 )) goto end;
  goto loc_22;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  if (!( 1+v7 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc_CP_26;
 }
 if (nondet_bool()) {
  if (!( v4 <= v7 )) goto end;
  goto loc_24;
 }
 goto end;
loc_27:
 if (nondet_bool()) {
  if (!( 1+v7 <= v2 )) goto end;
  v10 = v9;
  v8 = v7;
  v3 = 0;
  goto loc_CP_17;
 }
 if (nondet_bool()) {
  if (!( v2 <= v7 )) goto end;
  v12 = 0;
  v4 = 0;
  goto loc_CP_23;
 }
 goto end;
loc_28:
 if (nondet_bool()) {
  v9 = 50;
  v7 = 5;
  v2 = 0;
  goto loc_CP_26;
 }
 goto end;
loc_6:
end:
;
}
