int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 100 <= v1 )) goto end;
  v2 = 100;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 100 )) goto end;
  v3 = v1;
  v4 = v1;
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 200 <= v2 )) goto end;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= 200 )) goto end;
  v5 = v2;
  v2 = 1+v2;
  goto loc1;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v1 = 0;
  goto loc2;
 }
 goto end;
loc4:
end:
;
}
