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
goto loc4;
loc4:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 1+v6 <= v5 )) goto end;
  v4 = v1;
  v7 = v4;
  v9 = v7;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( v5 <= v6 )) goto end;
  v8 = v1;
  v1 = v1+v2;
  v2 = v8;
  v5 = 1+v5;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v3 = 30;
  v6 = v3;
  v1 = 1;
  v2 = 0;
  v5 = 2;
  goto loc2;
 }
 goto end;
loc1:
end:
;
}
