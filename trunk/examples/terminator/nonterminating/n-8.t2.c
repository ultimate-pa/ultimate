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
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v4 = v3;
  if (!( -1*v4+v9 <= 0 )) goto end;
  v4 = nondet();
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  v4 = v3;
  if (!( 0 <= -1-v4+v9 )) goto end;
  v4 = nondet();
  v7 = nondet();
  if (!( v7 <= 0 )) goto end;
  if (!( 0 <= v7 )) goto end;
  goto loc3;
 }
 if (nondet_bool()) {
  v4 = v3;
  if (!( 0 <= -1-v4+v9 )) goto end;
  v4 = nondet();
  v7 = nondet();
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v8 = nondet();
  v6 = v8;
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
  v5 = v3;
  v5 = nondet();
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
