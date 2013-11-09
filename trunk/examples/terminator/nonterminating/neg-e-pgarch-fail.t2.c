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
goto loc12;
loc12:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  v9 = 0;
  v7 = 1;
  v4 = nondet();
  v11 = v4;
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
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v3 = nondet();
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1+v8-v10 <= 1000 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1000 <= v8-v10 )) goto end;
  v12 = 1;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v12 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v12 <= 0 )) goto end;
  v6 = nondet();
  v8 = v6;
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v12 <= 0 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1 <= v12 )) goto end;
  v12 = 0;
  v5 = nondet();
  v10 = v5;
  goto loc9;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 1 <= v11 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v11 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v12 = 1;
  v1 = nondet();
  v9 = v2;
  v12 = 1;
  goto loc0;
 }
 goto end;
loc4:
end:
;
}
