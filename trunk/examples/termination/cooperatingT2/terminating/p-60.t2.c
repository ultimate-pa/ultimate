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
  goto loc_3;
 }
 goto end;
loc_CP_0:
 if (nondet_bool()) {
  if (!( 101-v4 <= 0 )) goto end;
  v3 = 0;
  v2 = v3;
  v1 = v2;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 0 <= 100-v4 )) goto end;
  if (!( 0 <= -1+v5 )) goto end;
  v4 = 1+v4;
  goto loc_2;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  goto loc_CP_0;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  v4 = 0;
  goto loc_4;
 }
 goto end;
loc_4:
 if (nondet_bool()) {
  if (!( 0 <= 100-v4 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v3 = 0;
  v2 = v3;
  v1 = v2;
  goto loc_1;
 }
 if (nondet_bool()) {
  if (!( 0 <= 100-v4 )) goto end;
  if (!( 0 <= -1+v5 )) goto end;
  v4 = 1+v4;
  goto loc_CP_0;
 }
 goto end;
loc_1:
end:
;
}
