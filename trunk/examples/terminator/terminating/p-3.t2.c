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
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( -1*v3+v4 <= 0 )) goto end;
  if (!( -1*v3+v4 <= 0 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( -1*v3+v4 <= 0 )) goto end;
  if (!( -1*v3+v4 <= 0 )) goto end;
  if (!( v3 <= v4 )) goto end;
  if (!( v4 <= v3 )) goto end;
  v3 = 1+v3;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v3+v4 )) goto end;
  v3 = 1+v3;
  goto loc6;
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
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
end:
;
}
