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
goto loc9;
loc9:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v3 <= 1 )) goto end;
  v6 = v7;
  goto loc2;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  v5 = nondet();
  v8 = v5;
  v5 = nondet();
  if (!( v3 <= 2*v8 )) goto end;
  if (!( 2*v8 <= v3 )) goto end;
  v3 = v8;
  if (!( v3 <= v8 )) goto end;
  if (!( v8 <= v3 )) goto end;
  if (!( 1 <= 2*v8 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  v4 = nondet();
  if (!( 1 <= v3 )) goto end;
  v5 = nondet();
  v8 = v5;
  v5 = nondet();
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
  v3 = 1+3*v3;
  if (!( v3 <= 1+3*v4 )) goto end;
  if (!( 1+3*v4 <= v3 )) goto end;
  goto loc7;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v2 = v2;
  goto loc8;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
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
