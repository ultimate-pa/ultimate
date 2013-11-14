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
goto loc_22;
loc_22:
 if (nondet_bool()) {
  goto loc_21;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_12;
 }
 goto end;
loc_CP_6:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  v5 = v14;
  v8 = v21;
  v23 = nondet();
  v19 = v23;
  v26 = v19;
  goto loc_11;
 }
 goto end;
loc_CP_13:
 if (nondet_bool()) {
  goto loc_19;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v17 = 1+v17;
  goto loc_CP_5;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_CP_6;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  v12 = nondet();
  v11 = 0;
  v10 = nondet();
  goto loc_4;
 }
 if (nondet_bool()) {
  v6 = nondet();
  goto loc_CP_9;
 }
 goto end;
loc_10:
 if (nondet_bool()) {
  if (!( 1+v13 <= v16 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v16 <= v13 )) goto end;
  goto loc_8;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  if (!( v26 <= 0 )) goto end;
  if (!( 0 <= v26 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v26 )) goto end;
  goto loc_10;
 }
 if (nondet_bool()) {
  if (!( 1+v26 <= 0 )) goto end;
  goto loc_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 1+v2 <= v17 )) goto end;
  v4 = 1;
  v4 = 0;
  goto loc_CP_13;
 }
 if (nondet_bool()) {
  if (!( v17 <= v2 )) goto end;
  v25 = nondet();
  goto loc_CP_9;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  goto loc_15;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  v1 = 1;
  v1 = 0;
  v17 = 1;
  goto loc_CP_5;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  v17 = 1+v17;
  goto loc_CP_2;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 1+v13 <= v16 )) goto end;
  goto loc_16;
 }
 if (nondet_bool()) {
  if (!( v16 <= v13 )) goto end;
  v12 = nondet();
  v11 = 0;
  v15 = 1;
  goto loc_16;
 }
 goto end;
loc_18:
 if (nondet_bool()) {
  if (!( v22 <= 0 )) goto end;
  if (!( 0 <= v22 )) goto end;
  goto loc_16;
 }
 if (nondet_bool()) {
  if (!( 1 <= v22 )) goto end;
  goto loc_17;
 }
 if (nondet_bool()) {
  if (!( 1+v22 <= 0 )) goto end;
  goto loc_17;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  goto loc_CP_13;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v3 <= v17 )) goto end;
  goto loc_CP_6;
 }
 if (nondet_bool()) {
  if (!( 1+v17 <= v3 )) goto end;
  v7 = v14;
  v9 = v21;
  v24 = nondet();
  v20 = v24;
  v22 = v20;
  goto loc_18;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  if (!( 2 <= v18 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 1 )) goto end;
  goto loc_15;
 }
 if (nondet_bool()) {
  if (!( v18 <= 1 )) goto end;
  if (!( 1 <= v18 )) goto end;
  v17 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  v18 = nondet();
  v4 = 0;
  v1 = v4;
  v3 = nondet();
  v2 = nondet();
  goto loc_20;
 }
 goto end;
loc_1:
end:
;
}
