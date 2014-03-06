// [](a -> <>b)
// a: ~#lock~1 = 1
// b: ~#lock~1 = 0 

// read~int(~#lock~1) = 1

implementation nondet() returns (#res : int)
{
    var ~r~1 : int;

    #res := ~r~1;
    return;
}

implementation KeAcquireSpinLock(#in~lp : $Pointer$, #in~ip : $Pointer$) returns ()
{
    var ~lp : $Pointer$;
    var ~ip : $Pointer$;

    ~lp := #in~lp;
    ~ip := #in~ip;
    call write~int(1, ~lp);
    call write~int(~irql~1, ~ip);
}

implementation KeReleaseSpinLock(#in~lp : $Pointer$, #in~i : int) returns ()
{
    var ~lp : $Pointer$;
    var ~i : int;

    ~lp := #in~lp;
    ~i := #in~i;
    call write~int(0, ~lp);
    ~irql~1 := ~i;
}

implementation IoAcquireCancelSpinLock(#in~ip : $Pointer$) returns ()
{
    var ~ip : $Pointer$;

    ~ip := #in~ip;
    ~csl~1 := 1;
    call write~int(~irql~1, ~ip);
}

implementation IoReleaseCancelSpinLock(#in~ip : int) returns ()
{
    var ~ip : int;

    ~ip := #in~ip;
    ~csl~1 := 0;
    ~irql~1 := ~ip;
}

implementation IoMarkIrpPending(#in~x : int) returns ()
{
    var ~x : int;

    ~x := #in~x;
}

implementation RemoveReferenceAndCompleteRequest(#in~x : int, #in~y : int) returns ()
{
    var ~x : int;
    var ~y : int;

    ~x := #in~x;
    ~y := #in~y;
}

implementation RemoveReferenceForDispatch(#in~x : int) returns ()
{
    var ~x : int;

    ~x := #in~x;
}

implementation ProcessConnectionStateChange(#in~x : int) returns ()
{
    var ~x : int;

    ~x := #in~x;
}

implementation init() returns ()
{
    var #t~ret8 : int;
    var #t~ret10 : int;
    var #t~ret12 : int;
    var #t~ret13 : int;
    var #t~ret14 : int;
    var #t~ret15 : int;
    var #t~ret16 : int;
    var #t~ret17 : int;
    var #t~ret18 : int;
    var #t~ret19 : int;
    var #t~ret20 : int;
    var #t~ret21 : int;

    ~keR~1 := 0;
    ~keA~1 := ~keR~1;
    call #t~ret8 := nondet();
    call write~int(#t~ret8, ~#lock~1);
    havoc #t~ret8;
    call #t~ret10 := nondet();
    call write~int(#t~ret10, ~#CancelIrql~1);
    havoc #t~ret10;
    call #t~ret12 := nondet();
    ~irql~1 := #t~ret12;
    havoc #t~ret12;
    call #t~ret13 := nondet();
    ~csl~1 := #t~ret13;
    havoc #t~ret13;
    call #t~ret14 := nondet();
    ~DeviceObject~9 := #t~ret14;
    havoc #t~ret14;
    call #t~ret15 := nondet();
    ~Irp~9 := #t~ret15;
    havoc #t~ret15;
    ~status~9 := 1;
    call #t~ret16 := nondet();
    ~status~9 := #t~ret16;
    havoc #t~ret16;
    ~keA~1 := 0;
    ~keR~1 := 0;
    call #t~ret17 := nondet();
    ~length~1 := #t~ret17;
    havoc #t~ret17;
    call #t~ret18 := nondet();
    ~NewTimeouts~1 := #t~ret18;
    havoc #t~ret18;
    call #t~ret19 := nondet();
    ~SerialStatus~1 := #t~ret19;
    havoc #t~ret19;
    call #t~ret20 := nondet();
    ~pBaudRate~1 := #t~ret20;
    havoc #t~ret20;
    call #t~ret21 := nondet();
    ~pLineControl~1 := #t~ret21;
    havoc #t~ret21;
    ~LData~1 := 0;
    ~LStop~1 := 0;
    ~LParity~1 := 0;
    ~Mask~1 := 255;
}

implementation body() returns (#res : int)
{
    var ~ddd2~13 : int;
    var #t~ret22 : int;
    var #t~ret23 : int;
    var #t~ret24 : int;
    var #t~ret25 : int;
    var #t~ret26 : int;
    var #t~ret29 : int;
    var #t~mem31 : int;
    var #t~ret32 : int;
    var #t~ret33 : int;
    var #t~ret36 : int;
    var #t~ret37 : int;
    var #t~mem39 : int;
    var #t~ret40 : int;
    var #t~ret41 : int;
    var #t~ret42 : int;
    var #t~ret43 : int;
    var #t~ret46 : int;
    var #t~post47 : int;
    var #t~ret48 : int;
    var #t~ret50 : int;
    var #t~mem51 : int;
    var #t~mem52 : int;
    var #t~mem54 : int;
    var #t~ret57 : int;
    var #t~ret58 : int;
    var #t~mem60 : int;
    var #t~ret61 : int;
    var #t~ret62 : int;
    var #t~ret63 : int;
    var #t~ret64 : int;
    var #t~ret65 : int;
    var #t~ret66 : int;
    var #t~mem70 : int;
    var #t~ret71 : int;
    var #t~ret72 : int;
    var #t~mem76 : int;
    var #t~ret77 : int;
    var #t~ret78 : int;
    var #t~ret79 : int;
    var #t~mem83 : int;
    var #t~ret84 : int;
    var #t~ret87 : int;
    var #t~ret88 : int;
    var #t~mem90 : int;
    var #t~ret91 : int;
    var #t~ret92 : int;
    var #t~ret93 : int;
    var #t~ret94 : int;
    var #t~mem98 : int;
    var #t~ret99 : int;
    var #t~ret100 : int;
    var #t~ret101 : int;
    var #t~mem105 : int;
    var #t~ret106 : int;
    var #t~ret107 : int;
    var #t~ret108 : int;
    var #t~ret109 : int;
    var #t~ret110 : int;
    var #t~ret111 : int;
    var #t~ret112 : int;
    var #t~ret113 : int;
    var #t~ret114 : int;
    var #t~ret115 : int;
    var #t~ret116 : int;
    var #t~ret117 : int;
    var #t~ret118 : int;
    var #t~ret119 : int;
    var #t~ret120 : int;
    var #t~mem124 : int;
    var #t~ret125 : int;
    var #t~ret126 : int;
    var #t~mem130 : int;
    var #t~ret131 : int;
    var ~rrr~85 : int;

    if (2 != ~status~9) {
        while (true)
        {
            if (!true) {
                break;
            }
            ~ddd2~13 := ~ddd2~13;
        }
    }
    if (true) {
        call #t~ret22 := nondet();
        if (#t~ret22 != 0) {
            havoc #t~ret22;
            call #t~ret23 := nondet();
            if (#t~ret23 != 0) {
                havoc #t~ret23;
                ~status~9 := 4;
            } else {
                havoc #t~ret23;
            }
        } else {
            havoc #t~ret22;
            call #t~ret24 := nondet();
            if (#t~ret24 != 0) {
                havoc #t~ret24;
                ~CurrentWaitIrp~1 := 0;
                call #t~ret25 := nondet();
                ~NewMask~1 := #t~ret25;
                havoc #t~ret25;
                call #t~ret26 := nondet();
                if (#t~ret26 != 0) {
                    havoc #t~ret26;
                    ~status~9 := 4;
                } else {
                    havoc #t~ret26;
                    ~keA~1 := 1;
                    ~keA~1 := 0;
                    call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                    call #t~ret29 := nondet();
                    ~NewMask~1 := #t~ret29;
                    havoc #t~ret29;
                    ~keR~1 := 1;
                    ~keR~1 := 0;
                    call #t~mem31 := read~int(~#OldIrql~9);
                    call KeReleaseSpinLock(~#lock~1, #t~mem31);
                    havoc #t~mem31;
                    if (~CurrentWaitIrp~1 != 0) {
                        call RemoveReferenceAndCompleteRequest(~CurrentWaitIrp~1, 2);
                    }
                }
            } else {
                havoc #t~ret24;
                call #t~ret32 := nondet();
                if (#t~ret32 != 0) {
                    havoc #t~ret32;
                    ~CurrentWaitIrp~1 := 0;
                    call #t~ret33 := nondet();
                    if (#t~ret33 != 0) {
                        havoc #t~ret33;
                        ~status~9 := 4;
                    } else {
                        havoc #t~ret33;
                    }
                    ~keA~1 := 1;
                    ~keA~1 := 0;
                    call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                    call #t~ret36 := nondet();
                    ~CurrentWaitIrp~1 := #t~ret36;
                    havoc #t~ret36;
                    call #t~ret37 := nondet();
                    if (#t~ret37 != 0) {
                        havoc #t~ret37;
                        ~status~9 := 1;
                    } else {
                        havoc #t~ret37;
                        call IoMarkIrpPending(~Irp~9);
                        ~status~9 := 7;
                    }
                    ~keR~1 := 1;
                    ~keR~1 := 0;
                    call #t~mem39 := read~int(~#OldIrql~9);
                    call KeReleaseSpinLock(~#lock~1, #t~mem39);
                    havoc #t~mem39;
                    if (~CurrentWaitIrp~1 != 0) {
                        call RemoveReferenceAndCompleteRequest(~CurrentWaitIrp~1, 2);
                    }
                } else {
                    havoc #t~ret32;
                    call #t~ret40 := nondet();
                    if (#t~ret40 != 0) {
                        havoc #t~ret40;
                        call #t~ret41 := nondet();
                        ~CancelIrp~1 := #t~ret41;
                        havoc #t~ret41;
                        call #t~ret42 := nondet();
                        ~Mask~1 := #t~ret42;
                        havoc #t~ret42;
                        call #t~ret43 := nondet();
                        if (#t~ret43 != 0) {
                            havoc #t~ret43;
                            ~status~9 := 4;
                        } else {
                            havoc #t~ret43;
                        }
                        if (~bitwiseAnd(~Mask~1, 10) != 0) {
                            ~keA~1 := 1;
                            ~keA~1 := 0;
                            call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                            call #t~ret46 := nondet();
                            ~length~1 := #t~ret46;
                            havoc #t~ret46;
                            while (true)
                            {
                                if (!(~length~1 > 0)) {
                                    break;
                                }
                                #t~post47 := ~length~1;
                                ~length~1 := #t~post47 - 1;
                                havoc #t~post47;
                                call #t~ret48 := nondet();
                                ~CancelIrp~1 := #t~ret48;
                                havoc #t~ret48;
                                call IoAcquireCancelSpinLock(~#CancelIrql~1);
                                call #t~ret50 := nondet();
                                if (#t~ret50 != 0) {
                                    havoc #t~ret50;
                                    call #t~mem51 := read~int(~#CancelIrql~1);
                                    call IoReleaseCancelSpinLock(#t~mem51);
                                    havoc #t~mem51;
                                } else {
                                    havoc #t~ret50;
                                    call #t~mem52 := read~int(~#CancelIrql~1);
                                    call IoReleaseCancelSpinLock(#t~mem52);
                                    havoc #t~mem52;
                                    ~keR~1 := 1;
                                    ~keR~1 := 0;
                                    call #t~mem54 := read~int(~#OldIrql~9);
                                    call KeReleaseSpinLock(~#lock~1, #t~mem54);
                                    havoc #t~mem54;
                                    call RemoveReferenceAndCompleteRequest(~CancelIrp~1, 11);
                                    ~keA~1 := 1;
                                    ~keA~1 := 0;
                                    call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                }
                            }
                            ~CancelIrp~1 := 0;
                            call #t~ret57 := nondet();
                            if (#t~ret57 != 0) {
                                havoc #t~ret57;
                                call #t~ret58 := nondet();
                                ~CancelIrp~1 := #t~ret58;
                                havoc #t~ret58;
                            } else {
                                havoc #t~ret57;
                            }
                            ~keR~1 := 1;
                            ~keR~1 := 0;
                            call #t~mem60 := read~int(~#OldIrql~9);
                            call KeReleaseSpinLock(~#lock~1, #t~mem60);
                            havoc #t~mem60;
                            if (~CancelIrp~1 != 0) {
                                call RemoveReferenceAndCompleteRequest(~CancelIrp~1, 11);
                            }
                        }
                    } else {
                        havoc #t~ret40;
                        call #t~ret61 := nondet();
                        if (#t~ret61 != 0) {
                            havoc #t~ret61;
                            call #t~ret62 := nondet();
                            if (#t~ret62 != 0) {
                                havoc #t~ret62;
                                ~status~9 := 4;
                            } else {
                                havoc #t~ret62;
                            }
                        } else {
                            havoc #t~ret61;
                            call #t~ret63 := nondet();
                            if (#t~ret63 != 0) {
                                havoc #t~ret63;
                                call #t~ret64 := nondet();
                                ~NewTimeouts~1 := #t~ret64;
                                havoc #t~ret64;
                                call #t~ret65 := nondet();
                                if (#t~ret65 != 0) {
                                    havoc #t~ret65;
                                    ~status~9 := 4;
                                } else {
                                    havoc #t~ret65;
                                }
                                call #t~ret66 := nondet();
                                if (#t~ret66 != 0) {
                                    havoc #t~ret66;
                                    ~status~9 := 15;
                                } else {
                                    havoc #t~ret66;
                                }
                                ~keA~1 := 1;
                                ~keA~1 := 0;
                                call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                ~keR~1 := 1;
                                ~keR~1 := 0;
                                call #t~mem70 := read~int(~#OldIrql~9);
                                call KeReleaseSpinLock(~#lock~1, #t~mem70);
                                havoc #t~mem70;
                            } else {
                                havoc #t~ret63;
                                call #t~ret71 := nondet();
                                if (#t~ret71 != 0) {
                                    havoc #t~ret71;
                                    call #t~ret72 := nondet();
                                    if (#t~ret72 != 0) {
                                        havoc #t~ret72;
                                        ~status~9 := 4;
                                    } else {
                                        havoc #t~ret72;
                                    }
                                    ~keA~1 := 1;
                                    ~keA~1 := 0;
                                    call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                    ~keR~1 := 1;
                                    ~keR~1 := 0;
                                    call #t~mem76 := read~int(~#OldIrql~9);
                                    call KeReleaseSpinLock(~#lock~1, #t~mem76);
                                    havoc #t~mem76;
                                } else {
                                    havoc #t~ret71;
                                    call #t~ret77 := nondet();
                                    if (#t~ret77 != 0) {
                                        havoc #t~ret77;
                                        call #t~ret78 := nondet();
                                        ~SerialStatus~1 := #t~ret78;
                                        havoc #t~ret78;
                                        call #t~ret79 := nondet();
                                        if (#t~ret79 != 0) {
                                            havoc #t~ret79;
                                            ~status~9 := 4;
                                        } else {
                                            havoc #t~ret79;
                                        }
                                        ~keA~1 := 1;
                                        ~keA~1 := 0;
                                        call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                        ~keR~1 := 1;
                                        ~keR~1 := 0;
                                        call #t~mem83 := read~int(~#OldIrql~9);
                                        call KeReleaseSpinLock(~#lock~1, #t~mem83);
                                        havoc #t~mem83;
                                    } else {
                                        havoc #t~ret77;
                                        call #t~ret84 := nondet();
                                        if (#t~ret84 != 0) {
                                            havoc #t~ret84;
                                            ~keA~1 := 1;
                                            ~keA~1 := 0;
                                            call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                            call #t~ret87 := nondet();
                                            if (#t~ret87 != 0) {
                                                havoc #t~ret87;
                                            } else {
                                                havoc #t~ret87;
                                                call #t~ret88 := nondet();
                                                if (#t~ret88 != 0) {
                                                    havoc #t~ret88;
                                                } else {
                                                    havoc #t~ret88;
                                                }
                                            }
                                            ~keR~1 := 1;
                                            ~keR~1 := 0;
                                            call #t~mem90 := read~int(~#OldIrql~9);
                                            call KeReleaseSpinLock(~#lock~1, #t~mem90);
                                            havoc #t~mem90;
                                            call ProcessConnectionStateChange(~DeviceObject~9);
                                        } else {
                                            havoc #t~ret84;
                                            call #t~ret91 := nondet();
                                            if (#t~ret91 != 0) {
                                                havoc #t~ret91;
                                                call #t~ret92 := nondet();
                                                if (#t~ret92 != 0) {
                                                    havoc #t~ret92;
                                                    ~status~9 := 4;
                                                } else {
                                                    havoc #t~ret92;
                                                }
                                            } else {
                                                havoc #t~ret91;
                                                call #t~ret93 := nondet();
                                                if (#t~ret93 != 0) {
                                                    havoc #t~ret93;
                                                    call #t~ret94 := nondet();
                                                    if (#t~ret94 != 0) {
                                                        havoc #t~ret94;
                                                        ~status~9 := 4;
                                                    } else {
                                                        havoc #t~ret94;
                                                        ~keA~1 := 1;
                                                        ~keA~1 := 0;
                                                        call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                                        ~keR~1 := 1;
                                                        ~keR~1 := 0;
                                                        call #t~mem98 := read~int(~#OldIrql~9);
                                                        call KeReleaseSpinLock(~#lock~1, #t~mem98);
                                                        havoc #t~mem98;
                                                    }
                                                } else {
                                                    havoc #t~ret93;
                                                    call #t~ret99 := nondet();
                                                    if (#t~ret99 != 0) {
                                                        havoc #t~ret99;
                                                        call #t~ret100 := nondet();
                                                        ~pBaudRate~1 := #t~ret100;
                                                        havoc #t~ret100;
                                                        call #t~ret101 := nondet();
                                                        if (#t~ret101 != 0) {
                                                            havoc #t~ret101;
                                                            ~status~9 := 4;
                                                        } else {
                                                            havoc #t~ret101;
                                                            ~keA~1 := 1;
                                                            ~keA~1 := 0;
                                                            call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                                            ~keR~1 := 1;
                                                            ~keR~1 := 0;
                                                            call #t~mem105 := read~int(~#OldIrql~9);
                                                            call KeReleaseSpinLock(~#lock~1, #t~mem105);
                                                            havoc #t~mem105;
                                                        }
                                                    } else {
                                                        havoc #t~ret99;
                                                        call #t~ret106 := nondet();
                                                        if (#t~ret106 != 0) {
                                                            havoc #t~ret106;
                                                            call #t~ret107 := nondet();
                                                            ~pLineControl~1 := #t~ret107;
                                                            havoc #t~ret107;
                                                            ~LData~1 := 0;
                                                            ~LStop~1 := 0;
                                                            ~LParity~1 := 0;
                                                            ~Mask~1 := 255;
                                                            call #t~ret108 := nondet();
                                                            if (#t~ret108 != 0) {
                                                                havoc #t~ret108;
                                                                ~status~9 := 4;
                                                            } else {
                                                                havoc #t~ret108;
                                                            }
                                                            if (true) {
                                                                call #t~ret109 := nondet();
                                                                if (#t~ret109 != 0) {
                                                                    havoc #t~ret109;
                                                                    ~LData~1 := 27;
                                                                    ~Mask~1 := 31;
                                                                } else {
                                                                    havoc #t~ret109;
                                                                    call #t~ret110 := nondet();
                                                                    if (#t~ret110 != 0) {
                                                                        havoc #t~ret110;
                                                                        ~LData~1 := 24;
                                                                        ~Mask~1 := 63;
                                                                    } else {
                                                                        havoc #t~ret110;
                                                                        call #t~ret111 := nondet();
                                                                        if (#t~ret111 != 0) {
                                                                            havoc #t~ret111;
                                                                            ~LData~1 := 25;
                                                                            ~Mask~1 := 127;
                                                                        } else {
                                                                            havoc #t~ret111;
                                                                            call #t~ret112 := nondet();
                                                                            if (#t~ret112 != 0) {
                                                                                havoc #t~ret112;
                                                                                ~LData~1 := 26;
                                                                            } else {
                                                                                havoc #t~ret112;
                                                                                ~status~9 := 15;
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                            if (~status~9 != 2) {
                                                            }
                                                            if (true) {
                                                                call #t~ret113 := nondet();
                                                                if (#t~ret113 != 0) {
                                                                    havoc #t~ret113;
                                                                    ~LParity~1 := 29;
                                                                } else {
                                                                    havoc #t~ret113;
                                                                    call #t~ret114 := nondet();
                                                                    if (#t~ret114 != 0) {
                                                                        havoc #t~ret114;
                                                                        ~LParity~1 := 31;
                                                                    } else {
                                                                        havoc #t~ret114;
                                                                        call #t~ret115 := nondet();
                                                                        if (#t~ret115 != 0) {
                                                                            havoc #t~ret115;
                                                                            ~LParity~1 := 33;
                                                                        } else {
                                                                            havoc #t~ret115;
                                                                            call #t~ret116 := nondet();
                                                                            if (#t~ret116 != 0) {
                                                                                havoc #t~ret116;
                                                                                ~LParity~1 := 35;
                                                                            } else {
                                                                                havoc #t~ret116;
                                                                                call #t~ret117 := nondet();
                                                                                if (#t~ret117 != 0) {
                                                                                    havoc #t~ret117;
                                                                                    ~LParity~1 := 37;
                                                                                } else {
                                                                                    havoc #t~ret117;
                                                                                    ~status~9 := 15;
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                            if (~status~9 != 2) {
                                                            }
                                                            if (true) {
                                                                call #t~ret118 := nondet();
                                                                if (#t~ret118 != 0) {
                                                                    havoc #t~ret118;
                                                                    ~LStop~1 := 32;
                                                                } else {
                                                                    havoc #t~ret118;
                                                                    call #t~ret119 := nondet();
                                                                    if (#t~ret119 != 0) {
                                                                        havoc #t~ret119;
                                                                        if (~LData~1 != 27) {
                                                                            ~status~9 := 15;
                                                                        }
                                                                        ~LStop~1 := 37;
                                                                    } else {
                                                                        havoc #t~ret119;
                                                                        call #t~ret120 := nondet();
                                                                        if (#t~ret120 != 0) {
                                                                            havoc #t~ret120;
                                                                            if (~LData~1 == 27) {
                                                                                ~status~9 := 15;
                                                                            }
                                                                            ~LStop~1 := 33;
                                                                        } else {
                                                                            havoc #t~ret120;
                                                                            ~status~9 := 15;
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                            if (~status~9 != 2) {
                                                            }
                                                            ~keA~1 := 1;
                                                            ~keA~1 := 0;
                                                            call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                                            ~keR~1 := 1;
                                                            ~keR~1 := 0;
                                                            call #t~mem124 := read~int(~#OldIrql~9);
                                                            call KeReleaseSpinLock(~#lock~1, #t~mem124);
                                                            havoc #t~mem124;
                                                        } else {
                                                            havoc #t~ret106;
                                                            call #t~ret125 := nondet();
                                                            if (#t~ret125 != 0) {
                                                                havoc #t~ret125;
                                                                call #t~ret126 := nondet();
                                                                if (#t~ret126 != 0) {
                                                                    havoc #t~ret126;
                                                                    ~status~9 := 4;
                                                                } else {
                                                                    havoc #t~ret126;
                                                                }
                                                                ~keA~1 := 1;
                                                                ~keA~1 := 0;
                                                                call KeAcquireSpinLock(~#lock~1, ~#OldIrql~9);
                                                                ~keR~1 := 1;
                                                                ~keR~1 := 0;
                                                                call #t~mem130 := read~int(~#OldIrql~9);
                                                                call KeReleaseSpinLock(~#lock~1, #t~mem130);
                                                                havoc #t~mem130;
                                                            } else {
                                                                havoc #t~ret125;
                                                                call #t~ret131 := nondet();
                                                                if (#t~ret131 != 0) {
                                                                    havoc #t~ret131;
                                                                } else {
                                                                    havoc #t~ret131;
                                                                    ~status~9 := 41;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if (~status~9 != 7) {
        if (~Irp~9 != 0) {
            call RemoveReferenceAndCompleteRequest(~Irp~9, ~status~9);
        }
    }
    call RemoveReferenceForDispatch(~DeviceObject~9);
    while (true)
    {
        if (!true) {
            break;
        }
        ~rrr~85 := ~rrr~85;
    }
}

implementation main() returns (#res : int)
{
}

var ~#lock~1 : $Pointer$;
var ~#CancelIrql~1 : $Pointer$;
var ~irql~1 : int;
var ~csl~1 : int;
var ~CurrentWaitIrp~1 : int;
var ~NewMask~1 : int;
var ~CancelIrp~1 : int;
var ~Mask~1 : int;
var ~length~1 : int;
var ~NewTimeouts~1 : int;
var ~SerialStatus~1 : int;
var ~pBaudRate~1 : int;
var ~pLineControl~1 : int;
var ~LData~1 : int;
var ~LStop~1 : int;
var ~LParity~1 : int;
var ~keA~1 : int;
var ~keR~1 : int;
var ~DeviceObject~9 : int;
var ~Irp~9 : int;
var ~status~9 : int;
var ~#OldIrql~9 : $Pointer$;
implementation ULTIMATE.init() returns ()
{
    #NULL := { base: 0, offset: 0 };
    #valid[0] := false;
    //~#lock~1 := 0;
    call write~int(0, ~#lock~1);
    //~#CancelIrql~1 := 0;
    call write~int(0, ~#CancelIrql~1);
    ~irql~1 := 0;
    ~csl~1 := 0;
    ~CurrentWaitIrp~1 := 0;
    ~NewMask~1 := 0;
    ~CancelIrp~1 := 0;
    ~Mask~1 := 0;
    ~length~1 := 0;
    ~NewTimeouts~1 := 0;
    ~SerialStatus~1 := 0;
    ~pBaudRate~1 := 0;
    ~pLineControl~1 := 0;
    ~LData~1 := 0;
    ~LStop~1 := 0;
    ~LParity~1 := 0;
    ~Mask~1 := 0;
    ~keA~1 := 0;
    ~keR~1 := 0;
    ~DeviceObject~9 := 0;
    ~Irp~9 := 0;
    ~status~9 := 0;
    //~#OldIrql~9 := 0;
    call write~int(0, ~#OldIrql~9);
}

function ~bitwiseAnd(a : int, b : int) returns (out : int);
type $Pointer$ = { base : int, offset : int };
var #NULL : { base : int, offset : int };
var #memory_$Pointer$ : [$Pointer$]$Pointer$;
procedure write~$Pointer$(#value : $Pointer$, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~$Pointer$ + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #value];
    ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];
    ensures #memory_bool == old(#memory_bool)[#ptr := #memory_bool[#ptr]];
    ensures #memory_real == old(#memory_real)[#ptr := #memory_real[#ptr]];

procedure read~$Pointer$(#ptr : $Pointer$) returns (#value : $Pointer$);
    requires #valid[#ptr!base];
    requires #sizeof~$Pointer$ + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_$Pointer$[#ptr];

var #memory_int : [$Pointer$]int;
procedure write~int(#value : int, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~INT + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];
    ensures #memory_int == old(#memory_int)[#ptr := #value];
    ensures #memory_bool == old(#memory_bool)[#ptr := #memory_bool[#ptr]];
    ensures #memory_real == old(#memory_real)[#ptr := #memory_real[#ptr]];

procedure read~int(#ptr : $Pointer$) returns (#value : int);
    requires #valid[#ptr!base];
    requires #sizeof~INT + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_int[#ptr];

var #memory_bool : [$Pointer$]bool;
procedure write~bool(#value : bool, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~BOOL + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];
    ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];
    ensures #memory_bool == old(#memory_bool)[#ptr := #value];
    ensures #memory_real == old(#memory_real)[#ptr := #memory_real[#ptr]];

procedure read~bool(#ptr : $Pointer$) returns (#value : bool);
    requires #valid[#ptr!base];
    requires #sizeof~BOOL + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_bool[#ptr];

var #memory_real : [$Pointer$]real;
procedure write~real(#value : real, #ptr : $Pointer$) returns ();
    requires #valid[#ptr!base];
    requires #sizeof~REAL + #ptr!offset <= #length[#ptr!base];
    modifies #memory_$Pointer$, #memory_int, #memory_bool, #memory_real;
    ensures #memory_$Pointer$ == old(#memory_$Pointer$)[#ptr := #memory_$Pointer$[#ptr]];
    ensures #memory_int == old(#memory_int)[#ptr := #memory_int[#ptr]];
    ensures #memory_bool == old(#memory_bool)[#ptr := #memory_bool[#ptr]];
    ensures #memory_real == old(#memory_real)[#ptr := #value];

procedure read~real(#ptr : $Pointer$) returns (#value : real);
    requires #valid[#ptr!base];
    requires #sizeof~REAL + #ptr!offset <= #length[#ptr!base];
    ensures #value == #memory_real[#ptr];

var #valid : [int]bool;
var #length : [int]int;
procedure ~free(~addr : $Pointer$) returns ();
    free requires ~addr!offset == 0;
    free requires #valid[~addr!base];
    ensures #valid == old(#valid)[~addr!base := false];
    modifies #valid;

procedure ~malloc(~size : int) returns (#res : $Pointer$);
    ensures old(#valid)[#res!base] == false;
    ensures #valid == old(#valid)[#res!base := true];
    ensures #res!offset == 0;
    ensures #res!base != 0;
    ensures #length == old(#length)[#res!base := ~size];
    modifies #valid, #length;

const #sizeof~$Pointer$ : int;
const #sizeof~INT : int;
const #sizeof~BOOL : int;
const #sizeof~REAL : int;
axiom #sizeof~$Pointer$ > 0;
axiom #sizeof~INT > 0;
axiom #sizeof~BOOL > 0;
axiom #sizeof~REAL > 0;
procedure nondet() returns (#res : int);
    modifies ;

procedure KeAcquireSpinLock(#in~lp : $Pointer$, #in~ip : $Pointer$) returns ();
    modifies #memory_int, #memory_$Pointer$, #memory_real, #memory_bool;

procedure KeReleaseSpinLock(#in~lp : $Pointer$, #in~i : int) returns ();
    modifies #memory_int, #memory_$Pointer$, #memory_real, #memory_bool, ~irql~1;

procedure IoAcquireCancelSpinLock(#in~ip : $Pointer$) returns ();
    modifies ~csl~1, #memory_int, #memory_$Pointer$, #memory_real, #memory_bool;

procedure IoReleaseCancelSpinLock(#in~ip : int) returns ();
    modifies ~csl~1, ~irql~1;

procedure IoMarkIrpPending(#in~x : int) returns ();
    modifies ;

procedure RemoveReferenceAndCompleteRequest(#in~x : int, #in~y : int) returns ();
    modifies ;

procedure RemoveReferenceForDispatch(#in~x : int) returns ();
    modifies ;

procedure ProcessConnectionStateChange(#in~x : int) returns ();
    modifies ;

procedure init() returns ();
    modifies ~keR~1, ~keA~1, #memory_int, #memory_$Pointer$, #memory_real, #memory_bool, ~irql~1, ~csl~1, ~DeviceObject~9, ~Irp~9, ~status~9, ~length~1, ~NewTimeouts~1, ~SerialStatus~1, ~pBaudRate~1, ~pLineControl~1, ~LData~1, ~LStop~1, ~LParity~1, ~Mask~1;

procedure body() returns (#res : int);
    modifies #memory_int, #memory_$Pointer$, #memory_real, #memory_bool, ~irql~1, ~csl~1, ~status~9, ~CurrentWaitIrp~1, ~NewMask~1, ~keA~1, ~keR~1, ~CancelIrp~1, ~Mask~1, ~length~1, ~NewTimeouts~1, ~SerialStatus~1, ~pBaudRate~1, ~pLineControl~1, ~LData~1, ~LStop~1, ~LParity~1;

procedure main() returns (#res : int);
    modifies ;

procedure ULTIMATE.init() returns ();
    modifies #memory_int, #memory_$Pointer$, #memory_real, #memory_bool, #valid, #NULL, ~#lock~1, ~#CancelIrql~1, ~irql~1, ~csl~1, ~CurrentWaitIrp~1, ~NewMask~1, ~CancelIrp~1, ~Mask~1, ~length~1, ~NewTimeouts~1, ~SerialStatus~1, ~pBaudRate~1, ~pLineControl~1, ~LData~1, ~LStop~1, ~LParity~1, ~keA~1, ~keR~1, ~DeviceObject~9, ~Irp~9, ~status~9, ~#OldIrql~9;
    modifies ;

procedure ULTIMATE.start() returns ();
    modifies ;

