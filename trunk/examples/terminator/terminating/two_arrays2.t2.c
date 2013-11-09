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
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  goto loc15;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v2 = 1+v2;
  goto loc4;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( v1 <= v6 )) goto end;
  v2 = 0;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v1 )) goto end;
  v6 = 1+v6;
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( v1 <= v5 )) goto end;
  v6 = 0;
  v6 = 0;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v1 )) goto end;
  v5 = 1+v5;
  goto loc12;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v1 <= v4 )) goto end;
  v5 = 0;
  v5 = 0;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v1 )) goto end;
  v4 = 1+v4;
  goto loc16;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  v4 = 0;
  v4 = 0;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v2 = 1+v2;
  goto loc13;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = 0;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v3 = 1+v3;
  goto loc9;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v1 <= v8 )) goto end;
  v3 = 0;
  v3 = 0;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v1 )) goto end;
  v8 = 1+v8;
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v1 <= v7 )) goto end;
  v8 = 0;
  v8 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v1 )) goto end;
  v7 = 1+v7;
  goto loc0;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v2 = 0;
  v9 = nondet();
  v10 = nondet();
  v7 = 0;
  v7 = 0;
  goto loc0;
 }
 goto end;
loc3:
end:
;
}
