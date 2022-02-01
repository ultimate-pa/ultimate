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
goto loc_8;
loc_8:
 if (nondet_bool()) {
  goto loc_7;
 }
 goto end;
loc_CP_1:
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
  goto loc_3;
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
  goto loc_5;
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
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v9 = v1;
  v10 = v2;
  v11 = v3;
  v12 = 1+v4;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v9 = v1;
  v10 = v2;
  v11 = 1+v3;
  v12 = v4;
  goto loc_CP_1;
 }
 goto end;
loc_3:
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
  goto loc_4;
 }
 goto end;
loc_5:
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
  goto loc_0;
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
  goto loc_2;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v1 = v9;
  v2 = v10;
  v3 = v11;
  v4 = v12;
  v9 = v1;
  v10 = v2;
  v11 = v2;
  v12 = v1;
  goto loc_CP_1;
 }
 goto end;
loc_7:
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
  goto loc_6;
 }
 if (nondet_bool()) {
  goto loc_4;
 }
 if (nondet_bool()) {
  goto loc_0;
 }
 if (nondet_bool()) {
  goto loc_2;
 }
 if (nondet_bool()) {
  goto loc_3;
 }
 if (nondet_bool()) {
  goto loc_5;
 }
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_4:
end:
;
}
