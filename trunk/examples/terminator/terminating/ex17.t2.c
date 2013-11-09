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
goto loc18;
loc18:
 if (nondet_bool()) {
  goto loc17;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc9;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  goto loc11;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 100 <= v1 )) goto end;
  v2 = -2+v1;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 100 )) goto end;
  v1 = 1+v1;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v3 = 1+v3;
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  v5 = v3;
  v2 = v5;
  goto loc3;
 }
 if (nondet_bool()) {
  goto loc8;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  v3 = v2;
  goto loc6;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  goto loc12;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  goto loc10;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  v4 = 1+v4;
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  goto loc15;
 }
 if (nondet_bool()) {
  goto loc14;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  v6 = v4;
  v2 = v6;
  v7 = nondet();
  goto loc13;
 }
 if (nondet_bool()) {
  goto loc16;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( 1+v1 <= 0 )) goto end;
  v4 = v2;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  goto loc4;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  v1 = 0;
  goto loc2;
 }
 goto end;
loc4:
loc4:
end:
;
}
