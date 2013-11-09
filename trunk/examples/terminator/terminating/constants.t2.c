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
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v4 = v4;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  if (!( v5-v6 <= 0 )) goto end;
  v3 = v7;
  v1 = v3;
  goto loc6;
 }
 if (nondet_bool()) {
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  if (!( 0 <= -1+v5-v6 )) goto end;
  v2 = v8;
  v1 = v2;
  v7 = v1;
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v2 = v8;
  v1 = v2;
  v7 = v1;
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v2 = v8;
  v1 = v2;
  v7 = v1;
  v1 = nondet();
  v6 = 1+v6;
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v3 = v7;
  v1 = v3;
  goto loc4;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v6 = 1+v6;
  goto loc3;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v5 = 400;
  v6 = 0;
  v7 = 0;
  goto loc3;
 }
 goto end;
loc4:
loc6:
end:
;
}
