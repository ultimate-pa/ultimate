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
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  v5 = v12;
  v6 = v3;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = -1+v7;
  v4 = nondet();
  v10 = v9;
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v5 = v11;
  v6 = v2;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  v5 = v11;
  v6 = v2;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = v2;
  v4 = nondet();
  v10 = v9;
  goto loc2;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v8 = nondet();
  v11 = nondet();
  v9 = nondet();
  v12 = nondet();
  v10 = v8;
  goto loc0;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v5 = v12;
  v6 = v3;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc1;
 }
 if (nondet_bool()) {
  v5 = v12;
  v6 = v3;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = -1+v2;
  v4 = nondet();
  v10 = v9;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc1:
loc1:
end:
;
}
