int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_4;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( v6 <= 1 )) goto end;
  v2 = 0;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 2 <= v6 )) goto end;
  v2 = 1;
  goto loc_2;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1 <= v4 )) goto end;
  v6 = 1+v6;
  goto loc_CP_1;
 }
 if (nondet_bool()) {
  if (!( v4 <= 0 )) goto end;
  v6 = -1+v6;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  v1 = 0;
  goto loc_3;
 }
 if (nondet_bool()) {
  v1 = 1;
  goto loc_3;
 }
 if (nondet_bool()) {
  v4 = nondet();
  if (!( 1 <= v4 )) goto end;
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  v5 = 2;
  v6 = v5;
  v4 = v3;
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v1 <= 0 )) goto end;
  goto loc_5;
 }
 goto end;
loc_5:
end:
;
}
