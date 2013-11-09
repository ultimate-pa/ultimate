int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v5 <= 0 )) goto end;
  v5 = -1*v5;
  v4 = v4-v5;
  v1 = v1-v5;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= 0 )) goto end;
  v4 = -1*v4;
  v3 = v3-v4;
  v5 = -1*v4+v5;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  v3 = -1*v3;
  v2 = v2-v3;
  v4 = -1*v3+v4;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 0 )) goto end;
  v2 = -1*v2;
  v1 = v1-v2;
  v3 = -1*v2+v3;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  v1 = -1*v1;
  v2 = -1*v1+v2;
  v5 = -1*v1+v5;
  goto loc6;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = nondet();
  v2 = nondet();
  v3 = nondet();
  v4 = nondet();
  v5 = nondet();
  if (!( 1 <= v1+v2+v3+v4+v5 )) goto end;
  v6 = v1+v2+v3+v4+v5;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc1;
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
end:
;
}
