extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
int pc;
int i; int Pdolen; int num; int DName;
int lptNamei;
int dcIdi;
int Pdoi;
int PdoType; int status;
set = 0;unset = 0;
int PPMakeDeviceName(int a, int b, int c, int d) { return __VERIFIER_nondet_int(); }
int IoCreateDevice(int a) { return __VERIFIER_nondet_int(); }
void ExFreePool(int a) {}
void PPBlockInits() {}
void PPUnblockInits() {}
void RtlInitUnicodeString(int a) {}
void main() {
  set = 1; set = 0;
  PPBlockInits();
  while (i < Pdolen) {
    DName = PPMakeDeviceName(lptNamei, PdoType, dcIdi, num);
    if (!DName) { break; }
    RtlInitUnicodeString(DName);
    status = IoCreateDevice(Pdoi); pc = 1; pc = 0;
    if (1 != status) {
      Pdoi = 0;
      if (2 == status) {
 ExFreePool(DName);
 num++;
 goto loc_continue;
      }
      break;
    } else {
      i++;
    }
  }
  num = 0;
  unset = 1; unset = 0;
  PPUnblockInits();
 loc_continue:0;
}
