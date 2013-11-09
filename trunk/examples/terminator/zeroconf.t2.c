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
goto loc23;
loc23:
 if (nondet_bool()) {
  goto loc22;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc15;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  v3 = 1;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v7 = 1+v7;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( v9 <= 1+v1 )) goto end;
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v6 = -1+v6;
  v8 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v8 = 1+v8;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  v9 = 1+v9;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  v2 = nondet();
  if (!( 0 <= v2 )) goto end;
  if (!( v2 <= 1 )) goto end;
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 1+v5 <= 1 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  goto loc9;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v6 = -1+v6;
  v8 = 0;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v8 = 1+v8;
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  v9 = 1+v9;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 1+v1 <= v7 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v7 <= v1 )) goto end;
  v5 = nondet();
  if (!( 0 <= v5 )) goto end;
  if (!( v5 <= 1 )) goto end;
  goto loc13;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  goto loc14;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v6 = -1+v6;
  v8 = 0;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( v4 <= 0 )) goto end;
  v8 = 1+v8;
  goto loc4;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( v6 <= 0 )) goto end;
  v9 = 1+v9;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  goto loc17;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v10 = -1+v10;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc18;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc20;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v2 = 0;
  v5 = 0;
  v7 = 0;
  v4 = nondet();
  if (!( 0 <= v4 )) goto end;
  if (!( v4 <= 1 )) goto end;
  goto loc19;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v9 = 1;
  v6 = 3+v9;
  v10 = nondet();
  if (!( 0 <= v10 )) goto end;
  v8 = 0;
  v1 = nondet();
  if (!( 0 <= v1 )) goto end;
  v4 = 0;
  v5 = 0;
  v2 = 0;
  v3 = 0;
  v7 = 0;
  goto loc2;
 }
 goto end;
loc21:
end:
;
}
