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
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( 2+v6 <= -1+2*v3 )) goto end;
  if (!( -1+2*v3 <= 2+v6 )) goto end;
  v4 = v3;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 2+v6 <= 2*v3 )) goto end;
  if (!( 2*v3 <= 2+v6 )) goto end;
  v4 = v3;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 3+v6 <= -1+2*v3 )) goto end;
  v4 = -1+v3;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+2*v3 <= 2+v6 )) goto end;
  v4 = 1+v3;
  goto loc_4;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v1 <= v2 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v4 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1+v4 <= v3 )) goto end;
  goto loc_3;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v3 = v4;
  v1 = v2;
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v3 = v4;
  v1 = v2;
  goto loc_CP_1;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( v3+v7 <= -1+2*v1 )) goto end;
  if (!( -1+2*v1 <= v3+v7 )) goto end;
  v2 = v1;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( v3+v7 <= 2*v1 )) goto end;
  if (!( 2*v1 <= v3+v7 )) goto end;
  v2 = v1;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v3+v7 <= -1+2*v1 )) goto end;
  v2 = -1+v1;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+2*v1 <= v3+v7 )) goto end;
  v2 = 1+v1;
  goto loc_0;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  if (!( 0 <= v6 )) goto end;
  if (!( v6 <= 3 )) goto end;
  if (!( 0 <= v3 )) goto end;
  if (!( v5 <= 3 )) goto end;
  if (!( 0 <= v7 )) goto end;
  if (!( v7 <= 3 )) goto end;
  if (!( 0 <= v1 )) goto end;
  if (!( v1 <= 3 )) goto end;
  goto loc_CP_1;
 }
 goto end;
end:
;
}
