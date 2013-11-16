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
goto loc_28;
loc_28:
 if (nondet_bool()) {
  goto loc_CP_18;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  goto loc_1;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  goto loc_CP_24;
 }
 goto end;
loc_CP_9:
 if (nondet_bool()) {
  goto loc_13;
 }
 goto end;
loc_CP_10:
 if (nondet_bool()) {
  goto loc_8;
 }
 goto end;
loc_CP_18:
 if (nondet_bool()) {
  goto loc_17;
 }
 goto end;
loc_CP_24:
 if (nondet_bool()) {
  goto loc_26;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v10 <= v9 )) goto end;
  if (!( v9 <= v10 )) goto end;
  v9 = 1+v9;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v10 )) goto end;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v9 )) goto end;
  goto loc_CP_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 1+v6 <= v9 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v9 <= v6 )) goto end;
  goto loc_2;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1 <= v13 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= 0 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v13 <= 0 )) goto end;
  if (!( 0 <= v13 )) goto end;
  goto loc_5;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_8:
 if (nondet_bool()) {
  if (!( 1+v11 <= v8 )) goto end;
  v6 = -1+v6;
  goto loc_CP_9;
 }
 if (nondet_bool()) {
  if (!( v8 <= v11 )) goto end;
  v4 = nondet();
  v8 = 1+v8;
  goto loc_CP_10;
 }
 goto end;
loc_11:
 if (nondet_bool()) {
  v14 = nondet();
  v2 = nondet();
  v5 = nondet();
  v13 = nondet();
  v12 = nondet();
  v5 = nondet();
  goto loc_CP_10;
 }
 goto end;
loc_12:
 if (nondet_bool()) {
  if (!( 1 <= v13 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= 0 )) goto end;
  goto loc_11;
 }
 if (nondet_bool()) {
  if (!( v13 <= 0 )) goto end;
  if (!( 0 <= v13 )) goto end;
  goto loc_7;
 }
 goto end;
loc_13:
 if (nondet_bool()) {
  if (!( 1+v6 <= v9 )) goto end;
  goto loc_7;
 }
 if (nondet_bool()) {
  if (!( v9 <= v6 )) goto end;
  v4 = nondet();
  v1 = nondet();
  v13 = nondet();
  goto loc_12;
 }
 goto end;
loc_14:
 if (nondet_bool()) {
  v5 = nondet();
  v2 = 1;
  v14 = v2;
  v12 = 0;
  goto loc_CP_9;
 }
 goto end;
loc_15:
 if (nondet_bool()) {
  if (!( 1+v5 <= 0 )) goto end;
  v20 = nondet();
  v21 = -1*v20;
  goto loc_14;
 }
 if (nondet_bool()) {
  if (!( 0 <= v5 )) goto end;
  v19 = nondet();
  v21 = v19;
  goto loc_14;
 }
 goto end;
loc_16:
 if (nondet_bool()) {
  v5 = nondet();
  v13 = nondet();
  goto loc_15;
 }
 goto end;
loc_17:
 if (nondet_bool()) {
  if (!( 1+v11 <= v6 )) goto end;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( v6 <= v11 )) goto end;
  v6 = 1+v6;
  goto loc_CP_18;
 }
 goto end;
loc_19:
 if (nondet_bool()) {
  if (!( 31 <= v18 )) goto end;
  goto loc_16;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 30 )) goto end;
  goto loc_16;
 }
 if (nondet_bool()) {
  if (!( v18 <= 30 )) goto end;
  if (!( 30 <= v18 )) goto end;
  goto loc_16;
 }
 goto end;
loc_20:
 if (nondet_bool()) {
  v18 = v7;
  v7 = 1+v7;
  goto loc_19;
 }
 goto end;
loc_21:
 if (nondet_bool()) {
  if (!( v10 <= v9 )) goto end;
  if (!( v9 <= v10 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v10 )) goto end;
  goto loc_20;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v9 )) goto end;
  goto loc_20;
 }
 goto end;
loc_22:
 if (nondet_bool()) {
  goto loc_21;
 }
 goto end;
loc_23:
 if (nondet_bool()) {
  v10 = 1+v10;
  goto loc_CP_24;
 }
 goto end;
loc_25:
 if (nondet_bool()) {
  if (!( 1+v3 <= v3+v17 )) goto end;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( 1+v3+v17 <= v3 )) goto end;
  goto loc_23;
 }
 if (nondet_bool()) {
  if (!( v3+v17 <= v3 )) goto end;
  if (!( v3 <= v3+v17 )) goto end;
  goto loc_22;
 }
 goto end;
loc_26:
 if (nondet_bool()) {
  if (!( v11 <= v10 )) goto end;
  goto loc_22;
 }
 if (nondet_bool()) {
  if (!( v10 <= -1+v11 )) goto end;
  v15 = nondet();
  v16 = nondet();
  v3 = v15+v16;
  v17 = nondet();
  goto loc_25;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  if (!( 1+v11 <= v9 )) goto end;
  goto loc_27;
 }
 if (nondet_bool()) {
  if (!( v9 <= v11 )) goto end;
  v7 = 0;
  goto loc_CP_3;
 }
 goto end;
loc_27:
end:
;
}
