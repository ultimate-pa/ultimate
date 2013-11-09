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
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v5 = v10;
  v6 = -1+v3;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  v5 = v10;
  v6 = -1+v3;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = -1+v3;
  v4 = nondet();
  v9 = v7;
  goto loc4;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v7 = nondet();
  v10 = nondet();
  v8 = nondet();
  v11 = nondet();
  v9 = v8;
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v5 = v11;
  v6 = v2;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc2;
 }
 if (nondet_bool()) {
  v5 = v11;
  v6 = v2;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = v3;
  v4 = nondet();
  v9 = v7;
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc2:
loc2:
end:
;
}
