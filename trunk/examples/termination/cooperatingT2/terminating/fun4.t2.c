int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
goto loc_4;
loc_4:
 if (nondet_bool()) {
  goto loc_3;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  if (!( -1+2*v2 <= v1+v4 )) goto end;
  if (!( v1+v4 <= 2*v2 )) goto end;
  v3 = v2;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+v1+v4 <= -1+2*v2 )) goto end;
  v3 = -1+v2;
  goto loc_0;
 }
 if (nondet_bool()) {
  if (!( 1+2*v2 <= v1+v4 )) goto end;
  v3 = 1+v2;
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  if (!( 1+v2 <= v3 )) goto end;
  goto loc_2;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= v2 )) goto end;
  goto loc_2;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v2 = v3;
  goto loc_CP_1;
 }
 goto end;
loc_3:
 if (nondet_bool()) {
  if (!( 0 <= v4 )) goto end;
  if (!( v4 <= 3 )) goto end;
  if (!( 0 <= v2 )) goto end;
  if (!( v2 <= 3 )) goto end;
  v1 = 2;
  goto loc_CP_1;
 }
 goto end;
end:
;
}
