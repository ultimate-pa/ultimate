int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
int v7 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 if (nondet_bool()) {
  v6 = -1+v2;
  v1 = nondet();
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 1+v6 <= v2 )) goto end;
  v4 = v1;
  v5 = v4;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v2 <= v6 )) goto end;
  v3 = nondet();
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v2 = 1+v3;
  goto loc2;
 }
 if (nondet_bool()) {
  v6 = -1+v3;
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v7 = 8;
  v2 = 0;
  v6 = 14;
  v1 = -1;
  goto loc2;
 }
 goto end;
loc4:
end:
;
}
