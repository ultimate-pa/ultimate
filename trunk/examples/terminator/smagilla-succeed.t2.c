int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  if (!( 1+v2 <= v3 )) goto end;
  v3 = -1+v3;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1 <= v1 )) goto end;
  v2 = -1+v2;
  v3 = -1+v3;
  v4 = 1+v4;
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  v1 = nondet();
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  goto loc4;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v2 = nondet();
  if (!( 1 <= v2 )) goto end;
  v5 = 8;
  v4 = 0;
  v3 = v5;
  goto loc0;
 }
 goto end;
loc3:
end:
;
}
