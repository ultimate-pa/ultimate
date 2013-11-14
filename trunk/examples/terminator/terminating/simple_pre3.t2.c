int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc_6;
loc_6:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 3 <= v1 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 2 )) goto end;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( v1 <= 2 )) goto end;
  if (!( 2 <= v1 )) goto end;
  v3 = 1;
  goto loc_2;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 2 <= v1 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= 1 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( v1 <= 1 )) goto end;
  if (!( 1 <= v1 )) goto end;
  v3 = 1;
  goto loc_2;
 }
 goto end;
loc_1:
 if (nondet_bool()) {
  v3 = 0;
  goto loc_2;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v1 = -1;
  v2 = 1;
  v1 = v2;
  goto loc_4;
 }
 goto end;
loc_3:
end:
;
}
