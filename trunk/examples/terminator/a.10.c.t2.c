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
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  if (!( v4 <= v3 )) goto end;
  if (!( v3 <= v4 )) goto end;
  v9 = v1;
  v10 = v2;
  v11 = v3;
  v12 = v4;
  goto loc3;
 }
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  if (!( 1+v3 <= v4 )) goto end;
  v9 = v1;
  v10 = v2;
  v11 = v3;
  v12 = v4;
  goto loc5;
 }
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  if (!( 1+v4 <= v3 )) goto end;
  v9 = v1;
  v10 = v2;
  v11 = v3;
  v12 = v4;
  goto loc5;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v9 = v1;
  v10 = v2;
  v11 = v3;
  v12 = 1+v4;
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v9 = v1;
  v10 = v2;
  v11 = 1+v3;
  v12 = v4;
  goto loc1;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v5 = nondet();
  v6 = nondet();
  v7 = nondet();
  v8 = nondet();
  v9 = v5;
  v10 = v6;
  v11 = v7;
  v12 = v8;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  if (!( v4 <= v3 )) goto end;
  v9 = v1;
  v10 = v2;
  v11 = v3;
  v12 = v4;
  goto loc0;
 }
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  if (!( 1+v3 <= v4 )) goto end;
  v9 = v1;
  v10 = v2;
  v11 = v3;
  v12 = v4;
  goto loc2;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v9 = v1;
  v10 = v2;
  v11 = v2;
  v12 = v1;
  goto loc1;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v5 = nondet();
  v6 = nondet();
  v9 = v1;
  v10 = v2;
  v11 = v5;
  v12 = v6;
  goto loc6;
 }
 if (nondet_bool()) {
  goto loc4;
 }
 if (nondet_bool()) {
  goto loc0;
 }
 if (nondet_bool()) {
  goto loc2;
 }
 if (nondet_bool()) {
  goto loc3;
 }
 if (nondet_bool()) {
  goto loc5;
 }
 if (nondet_bool()) {
  goto loc1;
 }
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc4:
loc4:
end:
;
}
