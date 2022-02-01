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
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_4:
 if (nondet_bool()) {
  v5 = v12;
  v6 = v3;
  if (!( 0 <= -1+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v4 = -1+v7;
  v4 = nondet();
  v10 = v9;
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v5 = v11;
  v6 = v2;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc_1;
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
  goto loc_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v8 = nondet();
  v11 = nondet();
  v9 = nondet();
  v12 = nondet();
  v10 = v8;
  goto loc_0;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v5 = v12;
  v6 = v3;
  if (!( v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc_1;
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
  goto loc_CP_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  goto loc_CP_4;
 }
 goto end;
loc_1:
end:
;
}
