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
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v5 <= 1+v1 )) goto end;
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  v6 = 1+v6;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  v6 = -1+v6;
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  v5 = 1+v5;
  v3 = v5;
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v3 = -1+v3;
  goto loc4;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v7 = -1+v7;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1+v6 <= 1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v6 )) goto end;
  v2 = nondet();
  if (!( 0 <= v2 )) goto end;
  if (!( v2 <= 1 )) goto end;
  goto loc7;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 1+v1 <= v6 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v6 <= v1 )) goto end;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v5 = 1;
  v3 = v5;
  v7 = nondet();
  if (!( 0 <= v7 )) goto end;
  v4 = 0;
  v1 = nondet();
  if (!( v1 <= 2 )) goto end;
  if (!( 2 <= v1 )) goto end;
  v6 = 1;
  goto loc3;
 }
 goto end;
loc1:
end:
;
}
