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
int v9 = nondet();
int v10 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v7 = v3;
  v5 = v4;
  if (!( v5-v7 <= 0 )) goto end;
  v7 = nondet();
  v5 = nondet();
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  v7 = v3;
  v5 = v4;
  if (!( 0 <= -1+v5-v7 )) goto end;
  v7 = nondet();
  v5 = nondet();
  v8 = nondet();
  if (!( v8 <= 0 )) goto end;
  if (!( 0 <= v8 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  v7 = v3;
  v5 = v4;
  if (!( 0 <= -1+v5-v7 )) goto end;
  v7 = nondet();
  v5 = nondet();
  v8 = nondet();
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v10 = nondet();
  v9 = nondet();
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
  v2 = v2;
  goto loc6;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v6 = v3;
  v6 = nondet();
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
