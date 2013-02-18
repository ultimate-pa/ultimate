/* iSafe */
/**
 * Example ntdrivers-simplified/cdaudio_simpl1.cil.c  from the 2012 sv-comp
 * where we added procedure declartions (Procedure declarations are not given
 * in the original file) and all but one procedure is removed.
 */

//int __VERIFIER_nondet_int()  ;
int s  ;
int UNLOADED  ;
int NP  ;
int DC  ;
int SKIP1  ;
int SKIP2  ;
int MPR1  ;
int MPR3  ;
int IPC  ;
int pended  ;
int compFptr  ;
int compRegistered  ;
int lowerDriverReturn  ;
int setEventCalled  ;
int customIrp  ;
int routine  ;
int myStatus  ;
int pirp  ;
int Executive ;
int Suspended ;
int KernelMode ;
int DeviceUsageTypePaging ;

void errorFn(void);
void _BLAST_init(void); 
int CdAudioSignalCompletion(int DeviceObject , int Irp , int Event ); 
int CdAudioStartDevice(int DeviceObject , int Irp ); 
int CdAudioPnp(int DeviceObject , int Irp ); 
int CdAudioDeviceControl(int DeviceObject , int Irp );
int CdAudioSendToNextDriver(int DeviceObject , int Irp ); 
int CdAudioIsPlayActive(int DeviceObject );
int CdAudio535DeviceControl(int DeviceObject , int Irp ); 
int AG_SetStatusAndReturn(int status , int Irp , int deviceExtension__TargetDeviceObject ); 
int CdAudio435DeviceControl(int DeviceObject , int Irp );
int CdAudioAtapiDeviceControl(int DeviceObject , int Irp ); 
void HpCdrProcessLastSession(int Toc );
int HPCdrCompletion(int DeviceObject , int Irp , int Context );
int CdAudioHPCdrDeviceControl(int DeviceObject , int Irp );
int CdAudioForwardIrpSynchronous(int DeviceObject , int Irp ); 
void CdAudioUnload(int DriverObject ); 
void stub_driver_init(void);
int main(void);
void stubMoreProcessingRequired(void); 
int IofCallDriver(int DeviceObject , int Irp ); 
void IofCompleteRequest(int Irp , int PriorityBoost ); 
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable , int Timeout );
int PoCallDriver(int DeviceObject , int Irp ); 
int ZwClose(int Handle );
int KeSetEvent(int Event , int Increment , int Wait );




#line 205 "cdaudio_simpl1.cil.c"
int CdAudioPnp(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation ;
  int irpSp__MinorFunction ;
  int Irp__IoStatus__Status ;
  int irpSp__Parameters__UsageNotification__Type ;
  int deviceExtension__PagingPathCountEvent ;
  int irpSp__Parameters__UsageNotification__InPath ;
  int deviceExtension__PagingPathCount ;
  int DeviceObject__Flags ;
  int irpSp ;
  int status ;
  int setPagable ;
  int tmp ;
  int tmp___0 ;

  {
#line 221
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
#line 222
  status = -1073741637;
#line 223
  if (irpSp__MinorFunction == 0) {
    goto switch_1_0;
  } else {
#line 226
    if (irpSp__MinorFunction == 22) {
      goto switch_1_22;
    } else {
      goto switch_1_default;
#line 231
      if (0) {
        switch_1_0: 
        {
#line 234
        status = CdAudioStartDevice(DeviceObject, Irp);
#line 235
        Irp__IoStatus__Status = status;
#line 236
        myStatus = status;
#line 237
        IofCompleteRequest(Irp, 0);
        }
#line 239
        return (status);
        switch_1_22: ;
#line 241
        if (irpSp__Parameters__UsageNotification__Type != DeviceUsageTypePaging) {
          {
#line 243
          tmp = CdAudioSendToNextDriver(DeviceObject, Irp);
          }
#line 245
          return (tmp);
        }
        {
#line 250
        status = KeWaitForSingleObject(deviceExtension__PagingPathCountEvent, Executive,
                                       KernelMode, 0, 0);
#line 252
        setPagable = 0;
        }
#line 254
        if (irpSp__Parameters__UsageNotification__InPath) {
#line 255
          if (deviceExtension__PagingPathCount != 1) {
            goto _L;
          }
        } else {
          _L: 
#line 262
          if (status == status) {
#line 265
            //DeviceObject__Flags |= 8192;
#line 266
            setPagable = 1;
          }
        }
        {
#line 270
        status = CdAudioForwardIrpSynchronous(DeviceObject, Irp);
        }
#line 272
        if (status >= 0) {
#line 273
          if (irpSp__Parameters__UsageNotification__InPath) {

          }
#line 278
          if (irpSp__Parameters__UsageNotification__InPath) {
#line 279
            if (deviceExtension__PagingPathCount == 1) {
#line 280
              //DeviceObject__Flags &= -8193;
            }
          }
        } else {
#line 288
          if (setPagable == 1) {
#line 289
            //DeviceObject__Flags &= -8193;
#line 290
            setPagable = 0;
          }
        }
        {
#line 296
        KeSetEvent(deviceExtension__PagingPathCountEvent, 0, 0);
#line 297
        IofCompleteRequest(Irp, 0);
        }
#line 299
        return (status);
        goto switch_1_break;
        switch_1_default: 
        {
#line 303
        tmp___0 = CdAudioSendToNextDriver(DeviceObject, Irp);
        }
#line 305
        return (tmp___0);
      } else {
        switch_1_break: ;
      }
    }
  }
#line 312
  return (0);
}
}