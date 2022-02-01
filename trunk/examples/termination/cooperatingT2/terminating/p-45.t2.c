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
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  if (!( v6 <= 0 )) goto end;
  v1 = v4;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( v5 <= 0 )) goto end;
  v5 = nondet();
  v1 = v4;
  if (!( v5 <= 0 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  v7 = nondet();
  v3 = nondet();
  if (!( 1 <= v5 )) goto end;
  if (!( 1 <= v6 )) goto end;
  v2 = v5;
  v5 = -2+v6;
  v6 = 1+v2;
  v2 = v5;
  v5 = -2+v6;
  v6 = 1+v2;
  if (!( v5 <= -1+v3 )) goto end;
  if (!( -1+v3 <= v5 )) goto end;
  if (!( v6 <= 1+v2 )) goto end;
  if (!( 1+v2 <= v6 )) goto end;
  if (!( v2 <= -2+v7 )) goto end;
  if (!( -2+v7 <= v2 )) goto end;
  if (!( 1 <= v7 )) goto end;
  if (!( 1 <= v3 )) goto end;
  goto loc_3;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  goto loc_CP_1;
 }
 goto end;
loc_2:
end:
;
}
