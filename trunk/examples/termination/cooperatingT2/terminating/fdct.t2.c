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
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 8 <= v2 )) goto end;
  v2 = 0;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 8 )) goto end;
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
  v1 = 4433;
  v16 = nondet();
  v1 = 6270;
  v1 = -15137;
  v16 = v12+v15;
  v17 = v13+v14;
  v18 = v12+v14;
  v19 = v13+v15;
  v1 = 9633;
  v20 = nondet();
  v1 = 2446;
  v12 = nondet();
  v1 = 16819;
  v13 = nondet();
  v1 = 25172;
  v14 = nondet();
  v1 = 12299;
  v15 = nondet();
  v1 = -7373;
  v16 = nondet();
  v1 = -20995;
  v17 = nondet();
  v1 = -16069;
  v18 = nondet();
  v1 = -3196;
  v19 = nondet();
  v18 = v18+v20;
  v19 = v19+v20;
  v2 = 1+v2;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 8 <= v2 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 8 )) goto end;
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
  v1 = 4433;
  v16 = nondet();
  v1 = 6270;
  v1 = -15137;
  v16 = v12+v15;
  v17 = v13+v14;
  v18 = v12+v14;
  v19 = v13+v15;
  v1 = 9633;
  v20 = nondet();
  v1 = 2446;
  v12 = nondet();
  v1 = 16819;
  v13 = nondet();
  v1 = 25172;
  v14 = nondet();
  v1 = 12299;
  v15 = nondet();
  v1 = -7373;
  v16 = nondet();
  v1 = -20995;
  v17 = nondet();
  v1 = -16069;
  v18 = nondet();
  v1 = -3196;
  v19 = nondet();
  v18 = v18+v20;
  v19 = v19+v20;
  v2 = 1+v2;
  goto loc_CP_1;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v3 = 8;
  v2 = 0;
  goto loc_CP_2;
 }
 goto end;
loc_4:
end:
;
}
