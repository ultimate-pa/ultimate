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
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v22 = v5;
  if (!( -1*v22 <= 0 )) goto end;
  v22 = nondet();
  v21 = v5;
  if (!( v21 <= 0 )) goto end;
  v21 = nondet();
  goto loc0;
 }
 if (nondet_bool()) {
  v22 = v5;
  if (!( -1*v22 <= 0 )) goto end;
  v22 = nondet();
  v21 = v5;
  if (!( 0 <= -1+v21 )) goto end;
  v21 = nondet();
  v20 = v5;
  v20 = nondet();
  v19 = nondet();
  v19 = nondet();
  v16 = nondet();
  if (!( -1*v16 <= 0 )) goto end;
  v16 = nondet();
  v15 = nondet();
  if (!( v15 <= 0 )) goto end;
  v15 = nondet();
  goto loc0;
 }
 if (nondet_bool()) {
  v22 = v5;
  if (!( 0 <= -1-v22 )) goto end;
  v22 = nondet();
  v18 = v5;
  v18 = nondet();
  v17 = nondet();
  v17 = nondet();
  v16 = nondet();
  if (!( -1*v16 <= 0 )) goto end;
  v16 = nondet();
  v15 = nondet();
  if (!( v15 <= 0 )) goto end;
  v15 = nondet();
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  v22 = v5;
  if (!( -1*v22 <= 0 )) goto end;
  v22 = nondet();
  v21 = v5;
  if (!( 0 <= -1+v21 )) goto end;
  v21 = nondet();
  v20 = v5;
  v20 = nondet();
  v19 = nondet();
  v19 = nondet();
  v16 = nondet();
  if (!( -1*v16 <= 0 )) goto end;
  v16 = nondet();
  v15 = nondet();
  if (!( 0 <= -1+v15 )) goto end;
  v15 = nondet();
  v14 = nondet();
  v14 = nondet();
  v13 = nondet();
  v13 = nondet();
  goto loc4;
 }
 if (nondet_bool()) {
  v22 = v5;
  if (!( -1*v22 <= 0 )) goto end;
  v22 = nondet();
  v21 = v5;
  if (!( 0 <= -1+v21 )) goto end;
  v21 = nondet();
  v20 = v5;
  v20 = nondet();
  v19 = nondet();
  v19 = nondet();
  v16 = nondet();
  if (!( 0 <= -1-v16 )) goto end;
  v16 = nondet();
  v12 = nondet();
  v12 = nondet();
  v11 = nondet();
  v11 = nondet();
  goto loc5;
 }
 if (nondet_bool()) {
  v22 = v5;
  if (!( 0 <= -1-v22 )) goto end;
  v22 = nondet();
  v18 = v5;
  v18 = nondet();
  v17 = nondet();
  v17 = nondet();
  v16 = nondet();
  if (!( -1*v16 <= 0 )) goto end;
  v16 = nondet();
  v15 = nondet();
  if (!( 0 <= -1+v15 )) goto end;
  v15 = nondet();
  v14 = nondet();
  v14 = nondet();
  v13 = nondet();
  v13 = nondet();
  goto loc6;
 }
 if (nondet_bool()) {
  v22 = v5;
  if (!( 0 <= -1-v22 )) goto end;
  v22 = nondet();
  v18 = v5;
  v18 = nondet();
  v17 = nondet();
  v17 = nondet();
  v16 = nondet();
  if (!( 0 <= -1-v16 )) goto end;
  v16 = nondet();
  v12 = nondet();
  v12 = nondet();
  v11 = nondet();
  v11 = nondet();
  goto loc7;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v23 = nondet();
  v2 = v23;
  v3 = v2;
  v4 = v3;
  v6 = v4;
  v7 = v6;
  v8 = v7;
  v9 = v8;
  v10 = v9;
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc1:
loc1:
end:
;
}
