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
int v8 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  v3 = v5;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v2 = nondet();
  v4 = v2;
  v2 = nondet();
  if (!( 0 <= v4 )) goto end;
  if (!( v4 <= 0 )) goto end;
  v8 = -1+v8;
  v6 = nondet();
  if (!( 2 <= v8 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v7 )) goto end;
  v2 = nondet();
  v4 = v2;
  v2 = nondet();
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v1 = v1;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v7 = -1+v7;
  v2 = nondet();
  v8 = v2;
  v2 = nondet();
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
end:
;
}
