
#include "../ctl.h"


extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));


#define NTSTATUS int
#define PIRP int
#define PDEVICE_OBJECT int
#define KIRQL int
#include<stdio.h>
#define STATUS_UNSUCCESSFUL 1
#define STATUS_SUCCESS 2
#define IOCTL_SERIAL_GET_WAIT_MASK 3
#define STATUS_BUFFER_TOO_SMALL 4
#define IOCTL_SERIAL_SET_WAIT_MASK 5
#define ULONG int
#define IOCTL_SERIAL_WAIT_ON_MASK 6
#define STATUS_PENDING 7
#define IOCTL_SERIAL_PURGE 8
#define PULONG int
#define IOCTL_SERIAL_GET_MODEMSTATUS 9
#define SERIAL_PURGE_RXABORT 10
#define STATUS_CANCELLED 11
#define IOCTL_SERIAL_SET_TIMEOUTS 12
#define PSERIAL_TIMEOUTS int
#define PSERIAL_STATUS int
#define PSERIAL_BAUD_RATE int
#define SERIAL_TIMEOUTS 14
#define STATUS_INVALID_PARAMETER 15
#define IOCTL_SERIAL_GET_TIMEOUTS 16
#define IOCTL_SERIAL_SET_DTR 17
#define IOCTL_SERIAL_CLR_DTR 18
#define IOCTL_SERIAL_GET_COMMSTATUS 19
#define IOCTL_SERIAL_GET_BAUD_RATE 20
#define IOCTL_SERIAL_SET_BAUD_RATE 21
#define IOCTL_SERIAL_SET_QUEUE_SIZE 22
#define SERIAL_BAUD_RATE int
#define IOCTL_SERIAL_SET_LINE_CONTROL 23
#define UCHAR int
#define SERIAL_LINE_CONTROL int
#define PSERIAL_LINE_CONTROL int
#define SERIAL_6_DATA 24
#define SERIAL_7_DATA 25
#define SERIAL_8_DATA 26
#define SERIAL_5_DATA 27
#define NO_PARITY 28
#define SERIAL_NONE_PARITY 29
#define EVEN_PARITY 30
#define SERIAL_EVEN_PARITY 31
#define ODD_PARITY 32
#define SERIAL_ODD_PARITY 33
#define SPACE_PARITY 34
#define SERIAL_SPACE_PARITY 35
#define MARK_PARITY 36
#define SERIAL_MARK_PARITY 37
#define STOP_BIT_1 28
#define STOP_BITS_2 29
#define STOP_BIT_3 30
#define STOP_BIT_4 31
#define SERIAL_1_STOP 32
#define SERIAL_2_STOP 33
#define SERIAL_3_STOP 34
#define SERIAL_4_STOP 35
#define STOP_BITS_1_5 36
#define SERIAL_1_5_STOP 37
#define SERIAL_LCR_BREAK 38
#define IOCTL_SERIAL_GET_LINE_CONTROL 39
#define IOCTL_SERIAL_SET_RTS 40
#define STATUS_NOT_SUPPORTED 41
#define PDEVICE_EXTENSION int
#define PCROM_DATA int
#define PASYNC_ADDRESS_DATA int
#define PISOCH_DETACH_DATA int
#define PISOCH_RESOURCE_DATA int
#define TRUE 1
#define FALSE 0
#define PIRB int
#define IRB int
#define CCHAR int
#define PBUS_RESET_IRP int
#define PDRIVER_CANCEL int
#define NonPagedPool 1
#define IO_NO_INCREMENT 2


int lock1;
int lock2;
int lock3;
int lock4;
int lock5;
int lock6;
int CancelIrql;
int irql;
int csl;
PDEVICE_OBJECT   DeviceObject;
PIRP             Irp;
NTSTATUS            ntStatus;
PDEVICE_EXTENSION   deviceExtension;
KIRQL               Irql;
int k1;
int k2;
int k3;
int k4;
int k5;
PCROM_DATA      CromData;
PASYNC_ADDRESS_DATA     AsyncAddressData;
PISOCH_RESOURCE_DATA    IsochResourceData;
PISOCH_DETACH_DATA      IsochDetachData;
ULONG                   i;
PIRB                pIrb;
PIRP                ResourceIrp;
CCHAR               StackSize;
PBUS_RESET_IRP  BusResetIrp;
PDRIVER_CANCEL  prevCancel;



int keA; int keR; int ioA; int ioR;
int phi_nSUC_ret; int phi_io_compl;

unsigned int pc;
// AG(A => AF(R)
//int __phi() { return CAG(COR(  CAF(CAP(keR == 1)), CAP(keA != 1) )); }
//int __phi() { return CAG(COR(  CAF(CAP(ioR == 1)), CAP(ioA != 1) )); }
/* prove that either IoCompleteRequest is called, 
   or a value other than STATUS_SUCCESS is returned. */
/*int __phi() { return COR(
			 CAF(CAP(phi_io_compl == 1)),
			 CAF(CAP(phi_nSUC_ret  == 1))); }*/


  keA = keR = ioA = ioR = 0;
  phi_nSUC_ret = 0; 
  phi_io_compl = 0;


void KeAcquireSpinLock(int * lp, int * ip) { keA = 1; keA = 0;
   (*lp) = 1;
   (*ip) = irql;
}

void KeReleaseSpinLock(int * lp, int i) { keR = 1; keR = 0;
   (*lp) = 0;
   irql = i;
}

void IoAcquireCancelSpinLock(int * ip) { ioA = 1; ioA = 0;
   csl = 1;
   (*ip) = irql;
}

void IoReleaseCancelSpinLock(int ip) { ioR = 1; ioR = 0;
   csl = 0;
   irql = ip;
}

int t1394_IsochCleanup(int a) { }
int ExAllocatePool(int a, int b) { }
int t1394Diag_PnpStopDevice(int a,int b) { }
int t1394_SubmitIrpSynch(int a, int b) { }
int IoFreeIrp(int a) { }
int IoSetDeviceInterfaceState() { }
int RtlZeroMemory(int a, int b) { }
int KeCancelTimer() { }
int IoAllocateIrp(int a, int b) { }
int IoFreeMdl() { }
int IoSetCancelRoutine(int a) { }
int ExFreePool0() { }
int ExFreePool1(int a) { }
int ExFreePool2(int a, int b) { }
int IoCompleteRequest(int a) { phi_io_compl = 1; }

int main() {
   if (__VERIFIER_nondet_int()) {

       // haven't stopped yet, lets do so
       ntStatus = t1394Diag_PnpStopDevice(DeviceObject, Irp);
   }

   ntStatus = IoSetDeviceInterfaceState();


   // lets free up any crom data structs we've allocated...
   KeAcquireSpinLock(&lock3, &Irql);

   k1 = __VERIFIER_nondet_int();
   while (k1>0) {

       CromData = __VERIFIER_nondet_int();

       // get struct off list
       k1--;

       // need to free up everything associated with this allocate...
       if (CromData)
       {
           if (__VERIFIER_nondet_int())
               ExFreePool0();

           if (__VERIFIER_nondet_int())
               IoFreeMdl();

           // we already checked CromData
           ExFreePool1(CromData);
       }
   }

   KeReleaseSpinLock(&lock3, Irql);

   KeAcquireSpinLock(&lock1, &Irql);

   k2 = __VERIFIER_nondet_int();
   while (k2>0) {

     AsyncAddressData = __VERIFIER_nondet_int();

       // get struct off list
       AsyncAddressData = __VERIFIER_nondet_int();
       k2--;

       // need to free up everything associated with this allocate...
       if (__VERIFIER_nondet_int())
           IoFreeMdl();

       if (__VERIFIER_nondet_int())
           ExFreePool0();

       if (__VERIFIER_nondet_int())
           ExFreePool0();

       if (AsyncAddressData)
           ExFreePool0();
   }

   KeReleaseSpinLock(&lock1, Irql);

   // free up any attached isoch buffers
   while (TRUE) {

       KeAcquireSpinLock(&lock4, &Irql);

       k3 = __VERIFIER_nondet_int();
       if (k3>0) {

	 IsochDetachData = __VERIFIER_nondet_int();
	 i = __VERIFIER_nondet_int();

           IsochDetachData = __VERIFIER_nondet_int();
           k3--;


           KeCancelTimer();
           KeReleaseSpinLock(&lock4, Irql);


           t1394_IsochCleanup(IsochDetachData);
       }
       else {

           KeReleaseSpinLock(&lock4, Irql);
           break;
       }
   }

   // remove any isoch resource data

   k4 = __VERIFIER_nondet_int();
   while (TRUE) {

       KeAcquireSpinLock(&lock5, &Irql);
       if (k4>0) {

           IsochResourceData = __VERIFIER_nondet_int();
           k4--;

           KeReleaseSpinLock(&lock5, Irql);


           if (IsochResourceData) {

	       pIrb = __VERIFIER_nondet_int();
               ResourceIrp = __VERIFIER_nondet_int();
               StackSize = __VERIFIER_nondet_int();
               ResourceIrp = IoAllocateIrp(StackSize, FALSE);

               if (ResourceIrp == NULL) {

               }
               else {

                   pIrb = ExAllocatePool(NonPagedPool, sizeof(IRB));

                   if (!pIrb) {

                       IoFreeIrp(ResourceIrp);
                   }
                   else {

                       RtlZeroMemory (pIrb, sizeof (IRB));

                       ntStatus = t1394_SubmitIrpSynch(ResourceIrp, pIrb);


                       ExFreePool1(pIrb);
                       IoFreeIrp(ResourceIrp);
                   }
               }
           }
       }
       else {

           KeReleaseSpinLock(&lock5, Irql);
           break;
       }
   }

   // get rid of any pending bus reset notify requests
   KeAcquireSpinLock(&lock6, &Irql);

   k5 = __VERIFIER_nondet_int();
   while (k5>0) {

       prevCancel = NULL;

       // get the irp off of the list
       BusResetIrp = __VERIFIER_nondet_int();
       k5--;


       // make this irp non-cancelable...
       prevCancel = IoSetCancelRoutine(NULL);


       // and complete it...
       IoCompleteRequest(IO_NO_INCREMENT);

       ExFreePool1(BusResetIrp);
   }

   KeReleaseSpinLock(&lock6, Irql);

   // free up the symbolic link
   if(ntStatus != STATUS_SUCCESS) { 
     phi_nSUC_ret = 1;
   }
   while(1) {}
}
