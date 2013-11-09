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
goto loc21;
loc21:
 if (nondet_bool()) {
  goto loc20;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  goto loc19;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v7 = 1;
  goto loc5;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v7 = 1;
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v7 = 1;
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v7 = 1;
  goto loc5;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc8;
 }
 if (nondet_bool()) {
  v7 = 0;
  goto loc5;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc7;
 }
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  goto loc6;
 }
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  goto loc4;
 }
 if (nondet_bool()) {
  goto loc12;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( v1 <= v4 )) goto end;
  v3 = 1+v3;
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v1 )) goto end;
  v4 = 1+v4;
  goto loc18;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = 1+v2;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v4 = 0;
  goto loc18;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v3 = 0;
  goto loc17;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v1 <= v3 )) goto end;
  v2 = 1+v2;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v1 )) goto end;
  v3 = 1+v3;
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  v2 = 0;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  v3 = 0;
  goto loc2;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  v1 = 2;
  v5 = nondet();
  v6 = nondet();
  v2 = 0;
  goto loc0;
 }
 goto end;
loc9:
end:
;
}
