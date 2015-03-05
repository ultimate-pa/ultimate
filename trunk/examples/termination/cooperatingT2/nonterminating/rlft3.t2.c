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
int v14 = nondet();
int v15 = nondet();
int v16 = nondet();
int v17 = nondet();
int v18 = nondet();
int v19 = nondet();
int v20 = nondet();
int v21 = nondet();
int v22 = nondet();
goto loc_26;
loc_26:
 if (nondet_bool()) {
  goto loc_25;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  goto loc_18;
 }
 goto end;
loc_CP_10:
 if (nondet_bool()) {
  goto loc_11;
 }
 goto end;
loc_CP_15:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_CP_19:
 if (nondet_bool()) {
  goto loc_20;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 0 <= v11 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= -1 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( v11 <= -1 )) goto end;
  if (!( -1 <= v11 )) goto end;
  goto loc_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v14 = nondet();
  v4 = nondet();
  v3 = nondet();
  v5 = nondet();
  v6 = nondet();
  goto loc_6;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v13 = 2-v8+v16;
  goto loc_5;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( v8 <= 1 )) goto end;
  if (!( 1 <= v8 )) goto end;
  v13 = 1;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 2 <= v8 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 1 )) goto end;
  goto loc_7;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v8 = 1+v8;
  goto loc_CP_9;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = nondet();
  v5 = nondet();
  v6 = nondet();
  goto loc_6;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  v13 = nondet();
  goto loc_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  if (!( v8 <= 1 )) goto end;
  if (!( 1 <= v8 )) goto end;
  v13 = 1;
  goto loc_12;
 }
 if (nondet_bool()) {
  if (!( 2 <= v8 )) goto end;
  goto loc_13;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 1 )) goto end;
  goto loc_13;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 2 <= v9 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= 1 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( v9 <= 1 )) goto end;
  if (!( 1 <= v9 )) goto end;
  goto loc_14;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  if (!( 1+v16 <= v8 )) goto end;
  v22 = v21;
  v21 = nondet();
  v18 = nondet();
  v9 = 1+v9;
  v10 = 2+v10;
  goto loc_CP_19;
 }
 if (nondet_bool()) {
  if (!( v8 <= v16 )) goto end;
  goto loc_17;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  v7 = 1+v7;
  goto loc_CP_15;
 }
 if (nondet_bool()) {
  goto loc_CP_9;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  v21 = 1;
  v18 = 0;
  goto loc_CP_19;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  v12 = 2-v7+v15;
  goto loc_21;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  if (!( v7 <= 1 )) goto end;
  if (!( 1 <= v7 )) goto end;
  v12 = 1;
  goto loc_21;
 }
 if (nondet_bool()) {
  if (!( 2 <= v7 )) goto end;
  goto loc_22;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 1 )) goto end;
  goto loc_22;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( 1+v15 <= v7 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( v7 <= v15 )) goto end;
  goto loc_23;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( 1+v16 <= v8 )) goto end;
  v7 = 1+v7;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( v8 <= v16 )) goto end;
  v13 = 1+v13;
  v8 = 1+v8;
  goto loc_CP_10;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 1+v15 <= v7 )) goto end;
  goto loc_CP_15;
 }
 if (nondet_bool()) {
  if (!( v7 <= v15 )) goto end;
  goto loc_CP_10;
 }
 goto end;
loc_24:
 if (nondet_bool()) {
  if (!( 2 <= v11 )) goto end;
  goto loc_CP_15;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 1 )) goto end;
  goto loc_CP_15;
 }
 if (nondet_bool()) {
  if (!( v11 <= 1 )) goto end;
  if (!( 1 <= v11 )) goto end;
  goto loc_CP_3;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  v1 = nondet();
  v2 = nondet();
  v17 = nondet();
  v22 = nondet();
  v20 = nondet();
  v19 = nondet();
  goto loc_24;
 }
 goto end;
loc_1:
end:
;
}
