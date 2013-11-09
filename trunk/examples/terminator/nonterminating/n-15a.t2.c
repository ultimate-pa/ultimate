int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc9;
loc9:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v4 = -1+v4;
  goto loc3;
 }
 if (nondet_bool()) {
  v4 = -1+v4;
  goto loc6;
 }
 if (nondet_bool()) {
  v4 = -1+v4;
  if (!( v4 <= 13 )) goto end;
  if (!( 13 <= v4 )) goto end;
  v4 = nondet();
  if (!( -1*v4 <= 0 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  v4 = -1+v4;
  if (!( v4 <= 13 )) goto end;
  if (!( 13 <= v4 )) goto end;
  v4 = nondet();
  if (!( 0 <= -1-v4 )) goto end;
  v1 = nondet();
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v2 = v2;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( -1*v4 <= 0 )) goto end;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v3 = v3;
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 0 <= -1-v4 )) goto end;
  v1 = nondet();
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc5:
loc5:
end:
;
}
