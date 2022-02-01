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
goto loc_8;
loc_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_5:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 64 <= v2 )) goto end;
  v1 = 7;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 64 )) goto end;
  v3 = nondet();
  v2 = 1+v2;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  v4 = nondet();
  v15 = nondet();
  v9 = nondet();
  v14 = nondet();
  v10 = nondet();
  v13 = nondet();
  v11 = nondet();
  v12 = nondet();
  v5 = v4+v11;
  v8 = v4-v11;
  v6 = v9+v10;
  v7 = v9-v10;
  v16 = nondet();
  v16 = v12+v15;
  v17 = v13+v14;
  v18 = v12+v14;
  v19 = v13+v15;
  v20 = nondet();
  v12 = nondet();
  v13 = nondet();
  v14 = nondet();
  v15 = nondet();
  v16 = nondet();
  v17 = nondet();
  v18 = nondet();
  v19 = nondet();
  v18 = v18+v20;
  v19 = v19+v20;
  v1 = -1+v1;
  goto loc_CP_5;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  v1 = 7;
  goto loc_CP_5;
 }
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  v4 = nondet();
  v15 = nondet();
  v9 = nondet();
  v14 = nondet();
  v10 = nondet();
  v13 = nondet();
  v11 = nondet();
  v12 = nondet();
  v5 = v4+v11;
  v8 = v4-v11;
  v6 = v9+v10;
  v7 = v9-v10;
  v16 = nondet();
  v16 = v12+v15;
  v17 = v13+v14;
  v18 = v12+v14;
  v19 = v13+v15;
  v20 = nondet();
  v12 = nondet();
  v13 = nondet();
  v14 = nondet();
  v15 = nondet();
  v16 = nondet();
  v17 = nondet();
  v18 = nondet();
  v19 = nondet();
  v18 = v18+v20;
  v19 = v19+v20;
  v1 = -1+v1;
  goto loc_CP_1;
 }
 goto end;
loc_7:
 if (nondet_bool()) {
  v3 = 0;
  v2 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_4:
end:
;
}
