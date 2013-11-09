int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 2 )) goto end;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 2 )) goto end;
  if (!( 2 <= v1 )) goto end;
  v3 = 1;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  v3 = 1;
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v3 = 0;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v1 = -1;
  v2 = 1;
  v1 = v2;
  goto loc4;
 }
 goto end;
loc3:
end:
;
}
