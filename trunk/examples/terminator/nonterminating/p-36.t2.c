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
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v17 = v8;
  v18 = v9;
  if (!( 0 <= -1-v17+v18 )) goto end;
  v17 = nondet();
  v18 = nondet();
  v16 = v8;
  v16 = nondet();
  v10 = nondet();
  v10 = nondet();
  v15 = v11;
  if (!( 0 <= -1+v15 )) goto end;
  v15 = nondet();
  v14 = v11;
  goto loc3;
 }
 if (nondet_bool()) {
  v17 = v8;
  v18 = v9;
  if (!( 0 <= -1-v17+v18 )) goto end;
  v17 = nondet();
  v18 = nondet();
  v16 = v8;
  v16 = nondet();
  v10 = nondet();
  v10 = nondet();
  v15 = v11;
  if (!( v15 <= 0 )) goto end;
  v15 = nondet();
  goto loc5;
 }
 if (nondet_bool()) {
  v17 = v8;
  v18 = v9;
  if (!( 0 <= -1-v17+v18 )) goto end;
  v17 = nondet();
  v18 = nondet();
  v16 = v8;
  v16 = nondet();
  v10 = nondet();
  v10 = nondet();
  v15 = v11;
  if (!( 0 <= -1+v15 )) goto end;
  v15 = nondet();
  v14 = v11;
  if (!( v14 <= 256 )) goto end;
  if (!( 256 <= v14 )) goto end;
  v14 = nondet();
  goto loc6;
 }
 if (nondet_bool()) {
  v17 = v8;
  v18 = v9;
  if (!( -1*v17+v18 <= 0 )) goto end;
  v17 = nondet();
  v18 = nondet();
  v7 = 0;
  v5 = v7;
  v4 = v5;
  goto loc7;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v3 = nondet();
  v19 = nondet();
  v12 = nondet();
  v1 = nondet();
  v2 = nondet();
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v6 = v6;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v14 = nondet();
  v13 = v11;
  v7 = v13;
  v13 = nondet();
  v5 = v7;
  v4 = v5;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
loc7:
end:
;
}
