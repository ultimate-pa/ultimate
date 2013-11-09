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
goto loc23;
loc23:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  goto loc18;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  goto loc20;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v5 = nondet();
  v6 = nondet();
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc5;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc7;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc11;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v8 = nondet();
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  if (!( 0 <= v8 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc12;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= 0 )) goto end;
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 1+v4 <= v1 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v1 <= v4 )) goto end;
  v8 = nondet();
  goto loc13;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= 0 )) goto end;
  goto loc7;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( v4 <= v3 )) goto end;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v4 )) goto end;
  v7 = 0;
  v1 = v3;
  goto loc3;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v8 = nondet();
  v2 = 1+v2;
  goto loc19;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  if (!( 1+v4 <= v2 )) goto end;
  goto loc19;
 }
 if (nondet_bool()) {
  if (!( v2 <= v4 )) goto end;
  v8 = nondet();
  v2 = 1+v2;
  goto loc21;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  if (!( v3 <= v1 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  goto loc21;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v3 )) goto end;
  goto loc21;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v2 = 1+v2;
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v5 <= v6 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  v7 = nondet();
  v1 = v2;
  goto loc22;
 }
 goto end;
loc17:
end:
;
}
