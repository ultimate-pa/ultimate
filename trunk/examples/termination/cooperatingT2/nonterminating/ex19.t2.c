int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_7;
loc_7:
 if (nondet_bool()) {
  goto loc_6;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v3 = -1+v3;
  v4 = -1+v4;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  if (!( v3 <= 0 )) goto end;
  if (!( 0 <= v3 )) goto end;
  goto loc_3;
 }
 if (nondet_bool()) {
  if (!( 1 <= v3 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  goto loc_0;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  goto loc_5;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 1+v2 <= v1 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= v2 )) goto end;
  goto loc_4;
 }
 if (nondet_bool()) {
  if (!( v1 <= v2 )) goto end;
  if (!( v2 <= v1 )) goto end;
  goto loc_4;
 }
 goto end;
loc_6:
 if (nondet_bool()) {
  v3 = v1;
  v4 = v2;
  goto loc_CP_1;
 }
 goto end;
loc_5:
end:
;
}
