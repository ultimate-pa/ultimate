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
goto loc_7;
loc_7:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  v5 = v2;
  v6 = v3;
  if (!( -1*v5+v6 <= 0 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v1 = nondet();
  goto loc_1;
 }
 if (nondet_bool()) {
  v5 = v2;
  v6 = v3;
  if (!( 0 <= -1-v5+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v9 = nondet();
  if (!( v9 <= 0 )) goto end;
  if (!( 0 <= v9 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  v5 = v2;
  v6 = v3;
  if (!( 0 <= -1-v5+v6 )) goto end;
  v5 = nondet();
  v6 = nondet();
  v9 = nondet();
  goto loc_4;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 1+v9 <= 0 )) goto end;
  goto loc_5;
 }
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc_5;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v4 = v2;
  v4 = nondet();
  goto loc_3;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v11 = nondet();
  v10 = nondet();
  v8 = v10;
  v7 = v11;
  goto loc_CP_0;
 }
 goto end;
loc_1:
end:
;
}
