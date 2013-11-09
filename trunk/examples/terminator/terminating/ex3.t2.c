int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( v3 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v3 )) goto end;
  v2 = 2+v2;
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 2 <= v3 )) goto end;
  v1 = 0;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( v3 <= 1 )) goto end;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v2 <= 2*v3 )) goto end;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 2*v3 <= v2 )) goto end;
  goto loc5;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v2 = 0;
  v3 = 10;
  goto loc3;
 }
 goto end;
loc4:
loc4:
end:
;
}
