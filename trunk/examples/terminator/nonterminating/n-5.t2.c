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
goto loc12;
loc12:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v11 <= 0 )) goto end;
  if (!( 0 <= v11 )) goto end;
  if (!( 0 <= -1-v13+v14 )) goto end;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( -1*v12+v13 <= 0 )) goto end;
  v1 = nondet();
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v12+v13 )) goto end;
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v10 = v5;
  if (!( 5-v10 <= 0 )) goto end;
  v10 = nondet();
  v4 = 1;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  v10 = v5;
  if (!( 0 <= 4-v10 )) goto end;
  v10 = nondet();
  v9 = v5;
  v9 = nondet();
  v4 = 0;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 0 <= -1-v13+v14 )) goto end;
  v10 = 0;
  if (!( 0 <= 4-v10 )) goto end;
  v10 = nondet();
  v9 = 0;
  v9 = nondet();
  v4 = 0;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( -1*v13+v14 <= 0 )) goto end;
  v12 = 1+v12;
  goto loc3;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v3 = v3;
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v13 = 1+v13;
  goto loc6;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 0 <= -1-v13+v14 )) goto end;
  v10 = 0;
  if (!( 0 <= 4-v10 )) goto end;
  v10 = nondet();
  v9 = 0;
  v9 = nondet();
  v4 = 0;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( -1*v13+v14 <= 0 )) goto end;
  v12 = 1+v12;
  goto loc3;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v8 = nondet();
  goto loc3;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v6 = -2;
  v10 = -1;
  if (!( 0 <= 4-v10 )) goto end;
  v10 = nondet();
  v9 = -1;
  v9 = nondet();
  v4 = 0;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v7 = -1+v6;
  v10 = v6;
  if (!( 0 <= 4-v10 )) goto end;
  v10 = nondet();
  v9 = v6;
  v9 = nondet();
  v4 = 0;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  v10 = v6;
  if (!( 5-v10 <= 0 )) goto end;
  v10 = nondet();
  v4 = 1;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v5 = -2;
  v10 = -1;
  if (!( 0 <= 4-v10 )) goto end;
  v10 = nondet();
  v9 = -1;
  v9 = nondet();
  v4 = 0;
  v2 = v4;
  v1 = v2;
  v11 = v1;
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc4:
end:
;
}
