// ****************************************************
//
//     Making Prophecies with Decision Predicates
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// ****************************************************

// Benchmark: win2bug.c
// Property: G(a => F r)

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
int nondet() { int x; return x; }
#define GetStatus nondet
#define IoInvalidateDeviceRelations nondet
#define KeWaitForSingleObject nondet
#define P4ReadRawIeee1284DeviceId nondet
#define HTPnpFindDeviceIdKeys nondet
#define HtFreePort nondet
#define HtRegGetDword nondet
#define HtTryAllocatePort nondet
#define SetFlags nondet

int WarmPollPeriod;
int status;
int polling;
int PowerStateIsAC;

void init() {
   WarmPollPeriod = nondet();
   status = nondet();
   polling = nondet();
   PowerStateIsAC = nondet();
}

int body() {


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


           if (nondet()) {

               // We've got it.  Now get a pointer to it.
               polling = 1;
               if(nondet()) {
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
                       if( nondet() ) {
                           break;
                       }
                       if( !PowerStateIsAC ) {
			 if(nondet()) polling = 0;
                           goto loc_continue;
                       }
                       if( STATUS_TIMEOUT == status ) {
                           if( nondet() ) {
                               // try to acquire port
                               if( HtTryAllocatePort() ) {
                                   requestRescan = FALSE;
                                   // check for something connected
                                   deviceStatus = GetStatus();
                                   if( nondet()) {
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
                                           if(nondet() ) {
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
		   loc_continue: { int ddd; ddd = ddd; }
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

int main() {}
