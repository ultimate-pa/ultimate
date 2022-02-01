extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
int WarmPollPeriod;
int status;
int polling;
int PowerStateIsAC;
void ExAcquireFastMutex() {}
void ExReleaseFastMutex() {}
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
   if( status>0 ) {
       ExAcquireFastMutex();
       __VERIFIER_nondet_int();
       ExReleaseFastMutex();
       WarmPollPeriod = __VERIFIER_nondet_int();
       if( WarmPollPeriod < 5 ) {
           WarmPollPeriod = 5;
       } else {
           if( WarmPollPeriod > 20 ) {
               WarmPollPeriod = 20;
           }
       }
       {
           if (__VERIFIER_nondet_int()) {
               polling = 1;
               if(__VERIFIER_nondet_int()) {
               {
                   int timeOut1;
                   int status;
                   int deviceStatus;
                   int devId;
                   int requestRescan;
                   const int pollingFailureThreshold = 10;
                   do {
                       if( PowerStateIsAC ) {
                       } else {
                       }
                       status = __VERIFIER_nondet_int();
                       if( __VERIFIER_nondet_int() ) {
                           break;
                       }
                       if( !PowerStateIsAC ) {
                           goto loc_continue;
                       }
                       if( (-1) == status ) {
         if(__VERIFIER_nondet_int())
          polling = 0;
                           if( __VERIFIER_nondet_int() ) {
                               if( __VERIFIER_nondet_int() ) {
                                   requestRescan = 0;
                                   deviceStatus = __VERIFIER_nondet_int();
                                   if( __VERIFIER_nondet_int()) {
                                   } else {
                                       devId = __VERIFIER_nondet_int();
                                       if( devId ) {
                                           int mfg, mdl, cls, des, aid, cid;
                                           __VERIFIER_nondet_int();
                                           if( mfg && mdl ) {
                                               requestRescan = 1;
                                           }
                                       } else {
                                       }
                                       if( requestRescan ) {
                                       } else {
                                           if(__VERIFIER_nondet_int() ) {
                                           }
                                       }
                                   }
                                   __VERIFIER_nondet_int( );
                                   if( requestRescan ) {
                                       __VERIFIER_nondet_int();
                                   }
                               } else {
                               }
                           } else {
                           }
                       }
     loc_continue: { }
                   } while( 1 );
               }
                   polling = 0;
               } else {
                   polling = 0;
               }
           } else {
           }
       }
   }
   polling = 1;
   while (1) {
       __VERIFIER_nondet_int();
   }
}
