int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc10;
loc10:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= v2 )) goto end;
  v2 = -1+v2;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 0 <= v1 )) goto end;
  v2 = 999;
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc7;
 }
 if (nondet_bool()) {
  if (!( 0 <= v4 )) goto end;
  v4 = -1+v4;
  goto loc8;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  v4 = 999;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  v3 = -1+v3;
  goto loc4;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v3 = 999;
  goto loc4;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v1 = 1;
  goto loc3;
 }
 goto end;
loc7:
end:
;
}
