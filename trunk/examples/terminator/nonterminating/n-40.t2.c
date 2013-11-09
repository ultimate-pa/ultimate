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
goto loc18;
loc18:
 if (nondet_bool()) {
  goto loc17;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 2-v10 <= 0 )) goto end;
  if (!( 0 <= 2-v9 )) goto end;
  v10 = 1+v10;
  v9 = 1+v9;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 2-v10 <= 0 )) goto end;
  if (!( 0 <= 2-v9 )) goto end;
  v10 = 1+v10;
  v9 = 1+v9;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v10 )) goto end;
  v10 = 1+v10;
  v9 = 1+v9;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v10 )) goto end;
  v10 = 1+v10;
  v9 = 1+v9;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v10 )) goto end;
  v10 = 1+v10;
  v9 = 1+v9;
  if (!( v10 <= 2 )) goto end;
  if (!( 2 <= v10 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( 0 <= 1-v10 )) goto end;
  v10 = 1+v10;
  v9 = 1+v9;
  if (!( v10 <= 2 )) goto end;
  if (!( 2 <= v10 )) goto end;
  if (!( v9 <= 2 )) goto end;
  if (!( 2 <= v9 )) goto end;
  v9 = 1;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 2-v10 <= 0 )) goto end;
  if (!( 3-v9 <= 0 )) goto end;
  v1 = nondet();
  goto loc16;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v2 = v2;
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v3 = v3;
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v4 = v4;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v9 <= 2 )) goto end;
  if (!( 2 <= v9 )) goto end;
  v9 = 1;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v5 = v5;
  goto loc9;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v6 = v6;
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v7 = v7;
  goto loc12;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( v9 <= 2 )) goto end;
  if (!( 2 <= v9 )) goto end;
  v9 = 1;
  goto loc10;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v8 = v8;
  goto loc13;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc16:
end:
;
}
