int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( -1*v4+v5 <= 0 )) goto end;
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v3 = nondet();
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  v3 = nondet();
  goto loc4;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v2 = v2;
  goto loc5;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
end:
;
}
