extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

#define STATUS_SUCCESS 1
#define STATUS_OBJECT_NAME_COLLISION 2
#define PC_IO 1
#define PC_NIO 0
int pc;
int i; int Pdolen; int num; int DName;
int lptNamei; //[5];
int dcIdi; // [5];
int Pdoi; //[5];
int PdoType; int status;

int set = 0;
int unset = 0;

// The Program
int PPMakeDeviceName(int a, int b, int c, int d) { return __VERIFIER_nondet_int(); }
int IoCreateDevice(int a) { return __VERIFIER_nondet_int(); }
void ExFreePool(int a) {}
void PPBlockInits() {}
void PPUnblockInits() {}
void RtlInitUnicodeString(int a) {}


int main() {
  set = 1; set = 0;
  PPBlockInits(); 
  while (i < Pdolen) { 
    DName = PPMakeDeviceName(lptNamei, PdoType, dcIdi, num); 
    if (!DName) { break; } 
    RtlInitUnicodeString(DName); 
    status = IoCreateDevice(Pdoi); pc = PC_IO; pc = PC_NIO;
    if (STATUS_SUCCESS != status) { 
      Pdoi = 0; 
      if (STATUS_OBJECT_NAME_COLLISION == status) { 
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
