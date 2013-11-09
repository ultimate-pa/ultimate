int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc13;
loc13:
 if (nondet_bool()) {
  goto loc12;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc6;
 }
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v5 = nondet();
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc11;
 }
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  if (!( v2 <= v1 )) goto end;
  goto loc9;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v2 )) goto end;
  v6 = nondet();
  v1 = 1+v1;
  goto loc4;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v4 = nondet();
  v3 = v4;
  v2 = v3;
  v1 = 0;
  goto loc4;
 }
 goto end;
loc3:
end:
;
}
