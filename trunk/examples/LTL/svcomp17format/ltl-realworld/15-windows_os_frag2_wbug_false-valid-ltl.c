extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int WarmPollPeriod;
int status;
int polling;
int PowerStateIsAC;
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
#define GetStatus __VERIFIER_nondet_int
#define IoInvalidateDeviceRelations __VERIFIER_nondet_int
#define KeWaitForSingleObject __VERIFIER_nondet_int
#define P4ReadRawIeee1284DeviceId __VERIFIER_nondet_int
#define HTPnpFindDeviceIdKeys __VERIFIER_nondet_int
#define HtFreePort __VERIFIER_nondet_int
#define HtRegGetDword __VERIFIER_nondet_int
#define HtTryAllocatePort __VERIFIER_nondet_int
#define SetFlags __VERIFIER_nondet_int


// Initialization routine
int __INITIALIZED = 0;
void env_init() {
	WarmPollPeriod = __VERIFIER_nondet_int();
	status = __VERIFIER_nondet_int();
	polling = __VERIFIER_nondet_int();
	PowerStateIsAC = __VERIFIER_nondet_int();
	__INITIALIZED = 1;
}


int main(){ 
   env_init();
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
               polling = 1;
               if(__VERIFIER_nondet_int()) {
//---------------------------------------------
               {
                   LARGE_INTEGER   timeOut1;
                   NTSTATUS        status;
                   UCHAR           deviceStatus;
                   PCHAR           devId;
                   BOOLEAN         requestRescan;
                   const ULONG     pollingFailureThreshold = 10; //pick an arbitrary but reasonable number
                   do {
                       if( PowerStateIsAC ) {
                       } else {
                       }
                       status = KeWaitForSingleObject();
                       if( __VERIFIER_nondet_int() ) {
                           break;
                       }
                       if( !PowerStateIsAC ) {
                           goto loc_continue;
                       }
                       if( STATUS_TIMEOUT == status ) {
						   if(__VERIFIER_nondet_int()) 
							   polling = 0;
						   
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
		   loc_continue: {  }
                   } while( TRUE );
               }
//---------------------------------------------
                   polling = 0;
               } else {
                   polling = 0;
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