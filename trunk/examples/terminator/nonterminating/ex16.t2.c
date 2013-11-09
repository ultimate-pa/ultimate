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
goto loc19;
loc19:
 if (nondet_bool()) {
  goto loc18;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+v18 <= v15 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v15 <= v18 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v15 <= v18 )) goto end;
  if (!( v18 <= v15 )) goto end;
  v7 = v15;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( v1 <= 4 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 5 <= v1 )) goto end;
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v12 = v9;
  v6 = v12;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( v14 <= 0 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1 <= v14 )) goto end;
  v17 = v14+v17;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1+v14 <= v3 )) goto end;
  v9 = v17;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( v3 <= v14 )) goto end;
  goto loc7;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1+v17 <= v14 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v14 <= v17 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( v14 <= v17 )) goto end;
  if (!( v17 <= v14 )) goto end;
  v9 = v14;
  goto loc6;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v11 = v8;
  v5 = v11;
  v14 = 3;
  v17 = -6;
  v3 = 0;
  goto loc11;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v13 <= 0 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1 <= v13 )) goto end;
  v16 = v13+v16;
  goto loc13;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 1+v13 <= v2 )) goto end;
  v8 = v16;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v2 <= v13 )) goto end;
  goto loc15;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 1+v16 <= v13 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v13 <= v16 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( v13 <= v16 )) goto end;
  if (!( v16 <= v13 )) goto end;
  v8 = v13;
  goto loc12;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v10 = v7;
  v1 = v10;
  v13 = -3;
  v16 = 4;
  v2 = 0;
  goto loc16;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( v15 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v15 )) goto end;
  v18 = v15+v18;
  goto loc1;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 1+v15 <= v4 )) goto end;
  v7 = v18;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v4 <= v15 )) goto end;
  goto loc17;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  v15 = 3;
  v18 = 3;
  v4 = 0;
  goto loc0;
 }
 goto end;
loc4:
end:
;
}
