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
  v1 = v1;
  goto loc2;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+2*v5 <= v4 )) goto end;
  if (!( v4 <= 1+2*v5 )) goto end;
  v4 = 1+3*v4;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 2*v5 <= v4 )) goto end;
  if (!( v4 <= 2*v5 )) goto end;
  v4 = v5;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v2 = v2;
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v3 = v3;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v5 = nondet();
  goto loc0;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v4 = nondet();
  if (!( 1 <= v4 )) goto end;
  goto loc1;
 }
 goto end;
end:
;
}
