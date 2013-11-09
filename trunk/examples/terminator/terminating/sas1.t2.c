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
loc5:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v3 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v3 )) goto end;
  v4 = nondet();
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( v3 <= v1 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v3 )) goto end;
  v1 = 1+v1;
  v2 = 0;
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  v1 = -1+v1;
  goto loc6;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v1 = 1+v1;
  v2 = 1+v2;
  goto loc5;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  if (!( 0 <= v4 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v1 = 0;
  goto loc6;
 }
 goto end;
loc4:
end:
;
}
