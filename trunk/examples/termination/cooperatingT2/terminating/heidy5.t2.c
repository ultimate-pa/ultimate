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
loc_CP_2:
 if (nondet_bool()) {
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( v2 <= 0 )) goto end;
  v1 = 1;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  v3 = -1+v3;
  goto loc_CP_2;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( v2 <= 0 )) goto end;
  goto loc_CP_2;
 }
 if (nondet_bool()) {
  if (!( 1 <= v2 )) goto end;
  v1 = 1+v1;
  goto loc_4;
 }
 goto end;
loc_5:
 if (nondet_bool()) {
  v1 = 0;
  goto loc_3;
 }
 goto end;
loc_4:
loc_1:
end:
;
}
