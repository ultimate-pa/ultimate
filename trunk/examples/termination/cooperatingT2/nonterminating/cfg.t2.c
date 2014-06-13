int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
goto loc_3;
loc_3:
 if (nondet_bool()) {
  goto loc_2;
 }
 goto end;
loc_CP_1:
 if (nondet_bool()) {
  v1 = 400+v1;
  if (!( 101 <= v1 )) goto end;
  goto loc_0;
 }
 goto end;
loc_0:
 if (nondet_bool()) {
  v1 = 300+v1;
  if (!( 101 <= v1 )) goto end;
  goto loc_CP_1;
 }
 goto end;
loc_2:
 if (nondet_bool()) {
  v1 = 200+v1;
  if (!( 101 <= v1 )) goto end;
  goto loc_0;
 }
 if (nondet_bool()) {
  v1 = 100+v1;
  if (!( 101 <= v1 )) goto end;
  goto loc_CP_1;
 }
 goto end;
end:
;
}
