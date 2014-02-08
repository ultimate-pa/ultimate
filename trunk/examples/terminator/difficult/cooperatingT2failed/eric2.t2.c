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
goto loc_7;
loc_7:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( 1 <= v14 )) goto end;
  v15 = -1+v14+v15;
  v14 = 0;
  v21 = 1+v21;
  v1 = 1+v1;
  goto loc_CP_3;
 }
 goto end;
loc_CP_3:
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  v18 = -1+v15+v18;
  v23 = v21+v23;
  v27 = 1+v27;
  v3 = v1+v3;
  v10 = 1+v10;
  v15 = 0;
  v21 = 0;
  v1 = 0;
  v15 = v15+v18;
  v21 = v21+v23+v27;
  v1 = v1+v3+v10;
  v18 = 0;
  v23 = 0;
  v27 = 0;
  v3 = 0;
  v10 = 0;
  goto loc_6;
 }
 if (nondet_bool()) {
  if (!( 1 <= v21 )) goto end;
  if (!( 1 <= v1 )) goto end;
  v16 = v15+v16;
  v24 = -1+v21+v24;
  v4 = -1+v1+v4;
  v7 = 1+v7;
  v15 = 0;
  v21 = 0;
  v1 = 0;
  goto loc_CP_4;
 }
 if (nondet_bool()) {
  v14 = v14+v15;
  v15 = 0;
  goto loc_CP_1;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  if (!( 1 <= v29 )) goto end;
  if (!( v29 <= v24 )) goto end;
  if (!( v29 <= v4 )) goto end;
  if (!( 1 <= v7 )) goto end;
  v19 = v16+v19;
  v20 = 1+v20;
  v26 = v24+v26-v29;
  v28 = -1+v28+v29;
  v6 = v4+v6-v29;
  v9 = -1+v7+v9;
  v11 = -1+v11+v29;
  v12 = 1+v12;
  v13 = 1+v13;
  v16 = 0;
  v24 = 0;
  v4 = 0;
  v7 = 0;
  v29 = nondet();
  v16 = v16+v19+v20;
  v24 = v24+v26+v28;
  v4 = v4+v6+v11+v13;
  v7 = v7+v9+v12;
  v19 = 0;
  v20 = 0;
  v26 = 0;
  v28 = 0;
  v6 = 0;
  v9 = 0;
  v11 = 0;
  v12 = 0;
  v13 = 0;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v16 )) goto end;
  v17 = -1+v16+v17;
  v22 = 1+v22;
  v25 = v24+v25;
  v2 = 1+v2;
  v5 = v4+v5;
  v8 = v7+v8;
  v16 = 0;
  v24 = 0;
  v4 = 0;
  v7 = 0;
  goto loc_2;
 }
 if (nondet_bool()) {
  v14 = v14+v16;
  v16 = 0;
  goto loc_CP_1;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 0 <= v14 )) goto end;
  if (!( v15 <= 0 )) goto end;
  if (!( 0 <= v15 )) goto end;
  if (!( v21 <= 0 )) goto end;
  if (!( 0 <= v21 )) goto end;
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  if (!( v16 <= 0 )) goto end;
  if (!( 0 <= v16 )) goto end;
  if (!( v24 <= 0 )) goto end;
  if (!( 0 <= v24 )) goto end;
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  if (!( v17 <= 0 )) goto end;
  if (!( 0 <= v17 )) goto end;
  if (!( v22 <= 0 )) goto end;
  if (!( 0 <= v22 )) goto end;
  if (!( v25 <= 0 )) goto end;
  if (!( 0 <= v25 )) goto end;
  if (!( v2 <= 0 )) goto end;
  if (!( 0 <= v2 )) goto end;
  if (!( v5 <= 0 )) goto end;
  if (!( 0 <= v5 )) goto end;
  if (!( v8 <= 0 )) goto end;
  if (!( 0 <= v8 )) goto end;
  if (!( v18 <= 0 )) goto end;
  if (!( 0 <= v18 )) goto end;
  if (!( v23 <= 0 )) goto end;
  if (!( 0 <= v23 )) goto end;
  if (!( v27 <= 0 )) goto end;
  if (!( 0 <= v27 )) goto end;
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  if (!( v10 <= 0 )) goto end;
  if (!( 0 <= v10 )) goto end;
  if (!( v19 <= 0 )) goto end;
  if (!( 0 <= v19 )) goto end;
  if (!( v20 <= 0 )) goto end;
  if (!( 0 <= v20 )) goto end;
  if (!( v26 <= 0 )) goto end;
  if (!( 0 <= v26 )) goto end;
  if (!( v28 <= 0 )) goto end;
  if (!( 0 <= v28 )) goto end;
  if (!( v6 <= 0 )) goto end;
  if (!( 0 <= v6 )) goto end;
  if (!( v9 <= 0 )) goto end;
  if (!( 0 <= v9 )) goto end;
  if (!( v11 <= 0 )) goto end;
  if (!( 0 <= v11 )) goto end;
  if (!( v12 <= 0 )) goto end;
  if (!( 0 <= v12 )) goto end;
  if (!( v13 <= 0 )) goto end;
  if (!( 0 <= v13 )) goto end;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v14 = v14+v17;
  v17 = 0;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  v15 = v15+v17;
  v21 = v21+v22;
  v1 = v1+v2;
  v17 = 0;
  v22 = 0;
  v2 = 0;
  goto loc_CP_3;
 }
 if (nondet_bool()) {
  v16 = v16+v17;
  v24 = v24+v25;
  v4 = v4+v5;
  v7 = v7+v8;
  v17 = 0;
  v25 = 0;
  v5 = 0;
  v8 = 0;
  goto loc_CP_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  goto loc_CP_3;
 }
 goto end;
end:
;
}
