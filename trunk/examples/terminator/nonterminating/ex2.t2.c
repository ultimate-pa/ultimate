int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+v2 <= 1024 )) goto end;
  v4 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1024 <= v2 )) goto end;
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v1 = 0;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc5;
 }
 if (nondet_bool()) {
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v3 = nondet();
  v2 = v3;
  goto loc3;
 }
 goto end;
loc5:
end:
;
}
