int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc_5;
loc_5:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  if (!( 0 <= -2-v4 )) goto end;
  v4 = 1+v4;
  v5 = 1+v5;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( -1-v4 <= 0 )) goto end;
  v1 = nondet();
  goto loc_3;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( 1+v5 <= 0 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v5 )) goto end;
  goto loc_1;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 0 <= -2+v2 )) goto end;
  if (!( 0 <= -2+v3 )) goto end;
  goto loc_CP_0;
 }
 if (nondet_bool()) {
  if (!( -1+v2 <= 0 )) goto end;
  v1 = nondet();
  goto loc_3;
 }
 goto end;
loc_3:
end:
;
}
