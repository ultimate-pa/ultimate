extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
void ExAcquireFastMutex() {}
void ExReleaseFastMutex() {}
int WarmPollPeriod;
int status;
int polling;
int PowerStateIsAC;
int Count;
int timeOut1;
int deviceStatus;
int devId;
int requestRescan;
   WarmPollPeriod = __VERIFIER_nondet_int();
   status = __VERIFIER_nondet_int();
   polling = __VERIFIER_nondet_int();
   PowerStateIsAC = __VERIFIER_nondet_int();
   Count = __VERIFIER_nondet_int();
int main() {
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
               if(__VERIFIER_nondet_int()) {
               {
         int timeOut1;
                   int status;
                   int deviceStatus;
                   int devId;
                   int requestRescan;
                   Count = __VERIFIER_nondet_int();
                   do {
                       if( PowerStateIsAC ) {
                       } else {
                       }
                       status = __VERIFIER_nondet_int();
                       if( __VERIFIER_nondet_int() ) {
                           break;
                       }
                       if( !PowerStateIsAC ) {
                       }
                       if( (-1) == status ) {
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
     mylabl: { int ddd; ddd = ddd; }
                   } while( --Count>0 );
               }
               } else {
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
