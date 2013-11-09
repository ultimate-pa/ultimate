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
goto loc11;
loc11:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v6 = v7;
  goto loc5;
 }
 if (nondet_bool()) {
  v2 = v2;
  goto loc6;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  v5 = 1;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v1 = v1;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  if (!( v5 <= 1 )) goto end;
  v8 = -1+v8;
  v5 = 0;
  goto loc3;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  if (!( v5 <= 1 )) goto end;
  v8 = -1+v8;
  v5 = 0;
  goto loc3;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 0 <= v8 )) goto end;
  if (!( v8 <= 0 )) goto end;
  v6 = v7;
  goto loc5;
 }
 if (nondet_bool()) {
  v3 = v3;
  goto loc8;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v4 = v4;
  goto loc9;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v8 = 1+v8;
  v5 = 1;
  v8 = -1*v8;
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v8 = -1*v8;
  goto loc7;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v8 = -1*v8;
  goto loc7;
 }
 goto end;
loc5:
loc5:
end:
;
}
