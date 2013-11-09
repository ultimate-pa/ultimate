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
goto loc10;
loc10:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v4 <= v2 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v4 )) goto end;
  v2 = 1+v2;
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 if (nondet_bool()) {
  v2 = -1+v2;
  goto loc1;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v2 <= v7 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v7 <= v2 )) goto end;
  v1 = nondet();
  v7 = 1+v7;
  goto loc7;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( v6 <= v5 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v5 <= v6 )) goto end;
  v1 = nondet();
  v7 = 1;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v6 = 10;
  v4 = 35;
  v8 = 285;
  v3 = nondet();
  v2 = v3;
  v5 = 0;
  goto loc3;
 }
 goto end;
loc8:
end:
;
}
