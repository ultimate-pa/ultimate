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
goto loc22;
loc22:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc19;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v8 <= 1+v5 )) goto end;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v4 <= v3 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v4 )) goto end;
  v3 = 1+v3;
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v8 = 1+v8;
  v9 = 0;
  v7 = 0;
  v6 = v8;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v9 = 0;
  v6 = -1+v6;
  goto loc4;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 2 <= v9 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v9 <= 1 )) goto end;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  if (!( 1 <= v2 )) goto end;
  v9 = 1+v9;
  goto loc4;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 2 <= v7 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v7 <= 1 )) goto end;
  goto loc7;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 1+v2 <= 1 )) goto end;
  v3 = -1+v3;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc2;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v7 = 1+v7;
  goto loc4;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc9;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v8 = 1+v8;
  v9 = 0;
  v7 = 0;
  v6 = v8;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  goto loc12;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  if (!( v1 <= 0 )) goto end;
  v9 = 0;
  v6 = -1+v6;
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 2 <= v9 )) goto end;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( v9 <= 1 )) goto end;
  goto loc13;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc14;
 }
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  if (!( 1 <= v1 )) goto end;
  v9 = 1+v9;
  goto loc12;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 2 <= v7 )) goto end;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v7 <= 1 )) goto end;
  goto loc15;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v2 = nondet();
  if (!( 0 <= v2 )) goto end;
  if (!( v2 <= 1 )) goto end;
  goto loc10;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc16;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( v1 <= 0 )) goto end;
  v7 = 1+v7;
  goto loc12;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc17;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  v1 = nondet();
  if (!( 0 <= v1 )) goto end;
  if (!( v1 <= 1 )) goto end;
  goto loc18;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  v8 = 1;
  v9 = 0;
  v6 = v8;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v7 = 0;
  v5 = nondet();
  if (!( 0 <= v5 )) goto end;
  v4 = nondet();
  if (!( 0 <= v4 )) goto end;
  if (!( v4 <= v5 )) goto end;
  v3 = nondet();
  if (!( v3 <= v4 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc1;
 }
 goto end;
loc20:
end:
;
}
