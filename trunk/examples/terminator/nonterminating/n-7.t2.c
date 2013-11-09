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
  if (!( 0 <= -1-v4+v5 )) goto end;
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  v3 = 1;
  v4 = 1+v4;
  goto loc0;
 }
 if (nondet_bool()) {
  if (!( -1*v4+v5 <= 0 )) goto end;
  v1 = nondet();
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 0 <= -1-v4+v5 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( -1*v4+v5 <= 0 )) goto end;
  v1 = nondet();
  goto loc4;
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
  v3 = 0;
  v5 = 1+v5;
  goto loc1;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v3 = 0;
  goto loc1;
 }
 goto end;
loc4:
loc4:
end:
;
}
