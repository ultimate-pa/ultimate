//#Safe
// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************
// Benchmark: win8.c
// Property: G(a => F r)

//@ ltl invariant positive: [](! AP(status != 0) || <> AP(polling!= 0));
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
#define NT_SUCCESS(s) s>0
#define STATUS_SUCCESS 1
#define STATUS_UNSUCCESSFUL 0
#define STATUS_TIMEOUT (-1)
#define LARGE_INTEGER int
#define NTSTATUS int
#define UCHAR int
#define PCHAR int
#define BOOLEAN int
#define ULONG int
#define NULL 0
#define FALSE 0
#define TRUE 1
void ExAcquireFastMutex() {}
void ExReleaseFastMutex() {}
#define GetStatus nondet
#define IoInvalidateDeviceRelations nondet
#define KeWaitForSingleObject nondet
#define P4ReadRawIeee1284DeviceId nondet
#define HTPnpFindDeviceIdKeys nondet
#define HtFreePort nondet
#define HtRegGetDword nondet
#define HtTryAllocatePort nondet
#define SetFlags nondet
#define CountLookup nondet
int WarmPollPeriod;
int status;
int polling;
int PowerStateIsAC;
int Count;
LARGE_INTEGER   timeOut1;
UCHAR           deviceStatus;
PCHAR           devId;
BOOLEAN         requestRescan;
   WarmPollPeriod = __VERIFIER_nondet_int();
   status = __VERIFIER_nondet_int();
   polling = __VERIFIER_nondet_int();
   PowerStateIsAC = __VERIFIER_nondet_int();
   Count = __VERIFIER_nondet_int();
int main() {
   if( NT_SUCCESS( status ) ) {
       ExAcquireFastMutex();
       SetFlags();
       ExReleaseFastMutex();
       WarmPollPeriod = HtRegGetDword();
       if( WarmPollPeriod < 5 ) {
           WarmPollPeriod = 5;
       } else {
           if( WarmPollPeriod > 20 ) {
               WarmPollPeriod = 20;
           }
       }
       {
           if (__VERIFIER_nondet_int()) {
               // We've got it.  Now get a pointer to it.
               if(__VERIFIER_nondet_int()) {
//---------------------------------------------
               {
  	  	   LARGE_INTEGER   timeOut1;
                   NTSTATUS        status;
                   UCHAR           deviceStatus;
                   PCHAR           devId;
                   BOOLEAN         requestRescan;
                   Count = CountLookup();
                   do {
                       if( PowerStateIsAC ) {
                       } else {
                       }
                       status = KeWaitForSingleObject();
                       if( __VERIFIER_nondet_int() ) {
                           break;
                       }
                       if( !PowerStateIsAC ) {
			 //goto mylabl;
                       }
                       if( STATUS_TIMEOUT == status ) {
                           if( __VERIFIER_nondet_int() ) {
                               // try to acquire port
                               if( HtTryAllocatePort() ) {
                                   requestRescan = FALSE;
                                   // check for something connected
                                   deviceStatus = GetStatus();
                                   if( __VERIFIER_nondet_int()) {
                                   } else {
                                       // we might have something connected
                                       // try a device ID to confirm
                                       devId = P4ReadRawIeee1284DeviceId();
                                       if( devId ) {
                                           PCHAR  mfg, mdl, cls, des, aid, cid;
                                           // RawIeee1284 string includes 2 bytes of length data at beginning
                                           HTPnpFindDeviceIdKeys();
                                           if( mfg && mdl ) {
                                               requestRescan = TRUE;
                                           }
                                       } else {
                                       }
                                       if( requestRescan ) {
                                       } else {
                                           if(__VERIFIER_nondet_int() ) {
                                           }
                                       }
                                   }
                                   HtFreePort( );
                                   if( requestRescan ) {
                                       IoInvalidateDeviceRelations();
                                   }
                               } else {
                               }
                           } else {
                           }
                       }
		   mylabl: { int ddd; ddd = ddd; }
                   } while( --Count>0 );
               }
//---------------------------------------------
               } else {
                   // error
               }
           } else {
           }
       }
   }
   // Failsafe
   polling = 1;
   while (1) {
       HTPnpFindDeviceIdKeys();
   }
}
int main() {}