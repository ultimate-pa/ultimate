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
int v23 = nondet();
int v24 = nondet();
int v25 = nondet();
int v26 = nondet();
int v27 = nondet();
int v28 = nondet();
int v29 = nondet();
int v30 = nondet();
int v31 = nondet();
int v32 = nondet();
goto loc_34;
loc_34:
 if (nondet_bool()) {
  goto loc_33;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_10:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_13:
 if (nondet_bool()) {
  goto loc_16;
 }
 goto end;
loc_CP_14:
 if (nondet_bool()) {
  goto loc_15;
 }
 goto end;
loc_CP_18:
 if (nondet_bool()) {
  goto loc_19;
 }
 goto end;
loc_CP_21:
 if (nondet_bool()) {
  goto loc_22;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v18 <= 0 )) goto end;
  v31 = nondet();
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 0 <= v18 )) goto end;
  v31 = v8;
  goto loc_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v8 = nondet();
  v15 = 1+v15;
  goto loc_CP_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 0 <= v18 )) goto end;
  v29 = nondet();
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 0 )) goto end;
  v29 = nondet();
  goto loc_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v20 <= v15 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( v15 <= v20 )) goto end;
  goto loc_4;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 0 <= v18 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 0 )) goto end;
  v8 = nondet();
  goto loc_7;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v15 = 1;
  goto loc_CP_3;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v16 <= 0 )) goto end;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 0 <= v16 )) goto end;
  v8 = nondet();
  goto loc_7;
 }
 goto end;
loc_9:
 if (nondet_bool()) {
  v11 = 1+v11;
  goto loc_CP_10;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v2 = nondet();
  goto loc_9;
 }
 if (nondet_bool()) {
  v2 = nondet();
  goto loc_9;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 8 <= v11 )) goto end;
  v26 = v2;
  v15 = 1+v15;
  goto loc_CP_13;
 }
 if (nondet_bool()) {
  if (!( 1+v11 <= 8 )) goto end;
  goto loc_11;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  if (!( 256 <= v15 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( v15 <= 255 )) goto end;
  v6 = nondet();
  v24 = 0;
  v2 = nondet();
  v11 = 0;
  goto loc_CP_10;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 1 <= v13 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= 0 )) goto end;
  goto loc_8;
 }
 if (nondet_bool()) {
  if (!( v13 <= 0 )) goto end;
  if (!( 0 <= v13 )) goto end;
  v13 = 1;
  v15 = 0;
  goto loc_CP_13;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  v27 = v32;
  v9 = v27;
  v3 = v9;
  v20 = 2+v22;
  v16 = 0;
  v18 = 1;
  v8 = v3;
  goto loc_17;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  if (!( 1+v19 <= 0 )) goto end;
  v32 = nondet();
  goto loc_20;
 }
 if (nondet_bool()) {
  if (!( 0 <= v19 )) goto end;
  v32 = v7;
  goto loc_20;
 }
 goto end;
loc_24:
 if (nondet_bool()) {
  v7 = nondet();
  v14 = 1+v14;
  goto loc_CP_21;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  if (!( 0 <= v19 )) goto end;
  v30 = nondet();
  goto loc_24;
 }
 if (nondet_bool()) {
  if (!( 1+v19 <= 0 )) goto end;
  v30 = nondet();
  goto loc_24;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  if (!( 1+v21 <= v14 )) goto end;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( v14 <= v21 )) goto end;
  goto loc_25;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  if (!( 0 <= v19 )) goto end;
  goto loc_27;
 }
 if (nondet_bool()) {
  if (!( 1+v19 <= 0 )) goto end;
  v7 = nondet();
  goto loc_27;
 }
 goto end;
loc_27:
 if (nondet_bool()) {
  v14 = 1;
  goto loc_CP_21;
 }
 goto end;
loc_28:
 if (nondet_bool()) {
  if (!( 1+v17 <= 0 )) goto end;
  goto loc_26;
 }
 if (nondet_bool()) {
  if (!( 0 <= v17 )) goto end;
  v7 = nondet();
  goto loc_27;
 }
 goto end;
loc_29:
 if (nondet_bool()) {
  v10 = 1+v10;
  goto loc_CP_18;
 }
 goto end;
loc_30:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc_29;
 }
 if (nondet_bool()) {
  v1 = nondet();
  goto loc_29;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( 8 <= v10 )) goto end;
  v25 = v1;
  v14 = 1+v14;
  goto loc_CP_14;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= 8 )) goto end;
  goto loc_30;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( 256 <= v14 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  if (!( v14 <= 255 )) goto end;
  v5 = nondet();
  v23 = 0;
  v1 = nondet();
  v10 = 0;
  goto loc_CP_18;
 }
 goto end;
loc_31:
 if (nondet_bool()) {
  if (!( 1 <= v13 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= 0 )) goto end;
  goto loc_28;
 }
 if (nondet_bool()) {
  if (!( v13 <= 0 )) goto end;
  if (!( 0 <= v13 )) goto end;
  v13 = 1;
  v14 = 0;
  goto loc_CP_14;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v28 = v31;
  v12 = v28;
  goto loc_32;
 }
 goto end;
loc_33:
 if (nondet_bool()) {
  v22 = 40;
  v4 = 0;
  v21 = v22;
  v17 = 0;
  v19 = 1;
  v7 = v4;
  goto loc_31;
 }
 goto end;
loc_32:
end:
;
}
