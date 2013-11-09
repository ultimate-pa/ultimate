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
  goto loc0;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( 1+v7 <= 0 )) goto end;
  v5 = 0;
  v3 = v5;
  v1 = v3;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 0 <= v7 )) goto end;
  v7 = -1*v6+v7;
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( -1*v6 <= 0 )) goto end;
  v5 = 0;
  v3 = v5;
  v1 = v3;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 0 <= -1-v6 )) goto end;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v4 = 0;
  v2 = v4;
  v1 = v2;
  goto loc5;
 }
 goto end;
loc5:
end:
;
}
