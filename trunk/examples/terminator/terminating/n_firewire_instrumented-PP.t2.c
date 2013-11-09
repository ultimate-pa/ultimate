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
goto loc15;
loc15:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = -1+v1;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  v3 = 1+v3;
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  v4 = 0;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v4 <= 2 )) goto end;
  if (!( v6 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 2 <= v4 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v4 <= 1 )) goto end;
  if (!( 1 <= v6 )) goto end;
  v4 = 1+v4;
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v5 <= v6 )) goto end;
  if (!( v6 <= v5 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v6 )) goto end;
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( v6 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v7 = -1+v7;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 3 <= v4 )) goto end;
  v3 = 1+v3;
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  v4 = 0;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( v4 <= 2 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 2 <= v4 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( v4 <= 1 )) goto end;
  if (!( 1 <= v5 )) goto end;
  v4 = 1+v4;
  goto loc8;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v6 = nondet();
  if (!( 0 <= v6 )) goto end;
  if (!( v6 <= 1 )) goto end;
  goto loc6;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v4 = 1+v4;
  goto loc8;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v7 = -1+v7;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc11;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v5 = nondet();
  if (!( 0 <= v5 )) goto end;
  if (!( v5 <= 1 )) goto end;
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  v4 = 0;
  v3 = 1;
  v2 = nondet();
  if (!( 1 <= v2 )) goto end;
  v1 = v2;
  v5 = 0;
  v6 = 0;
  goto loc1;
 }
 goto end;
loc13:
end:
;
}
