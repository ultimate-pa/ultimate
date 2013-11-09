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
int v11 = nondet();
int v12 = nondet();
goto loc7;
loc7:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v6 = v3;
  v7 = v4;
  if (!( -1*v6+v7 <= 0 )) goto end;
  v6 = nondet();
  v7 = nondet();
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  v6 = v3;
  v7 = v4;
  if (!( 0 <= -1-v6+v7 )) goto end;
  v6 = nondet();
  v7 = nondet();
  v10 = nondet();
  if (!( v10 <= 0 )) goto end;
  if (!( 0 <= v10 )) goto end;
  goto loc2;
 }
 if (nondet_bool()) {
  v6 = v3;
  v7 = v4;
  if (!( 0 <= -1-v6+v7 )) goto end;
  v6 = nondet();
  v7 = nondet();
  v10 = nondet();
  goto loc4;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v2 = v2;
  goto loc5;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v5 = v3;
  v5 = nondet();
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v12 = nondet();
  v11 = nondet();
  v9 = v11;
  v8 = v12;
  goto loc0;
 }
 goto end;
loc1:
end:
;
}
