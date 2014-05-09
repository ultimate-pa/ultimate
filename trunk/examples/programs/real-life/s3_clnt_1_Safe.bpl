//#Safe
/*
 * Date: 12.03.2014
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Program 
 *     ssh-simplified/s3_clnt_1_true-unreach-label.cil.c
 * from the SV-COMP repository. Translated to Boogie with the 
 * CASCL2BoogieTranslater plugin of Ultimate. Furthermore I removed all 
 * procedure calls and all procedures but one.
 *
 */


implementation ssl3_connect(#in~initial_state : int) returns (#res : int)
{
    var ~initial_state : int;
    var ~s__info_callback~7 : int;
    var ~s__in_handshake~7 : int;
    var ~s__state~7 : int;
    var ~s__new_session~7 : int;
    var ~s__server~7 : int;
    var ~s__version~7 : int;
    var ~s__type~7 : int;
    var ~s__init_num~7 : int;
    var ~s__bbio~7 : int;
    var ~s__wbio~7 : int;
    var ~s__hit~7 : int;
    var ~s__rwstate~7 : int;
    var ~s__init_buf___0~7 : int;
    var ~s__debug~7 : int;
    var ~s__shutdown~7 : int;
    var ~s__ctx__info_callback~7 : int;
    var ~s__ctx__stats__sess_connect_renegotiate~7 : int;
    var ~s__ctx__stats__sess_connect~7 : int;
    var ~s__ctx__stats__sess_hit~7 : int;
    var ~s__ctx__stats__sess_connect_good~7 : int;
    var ~s__s3__change_cipher_spec~7 : int;
    var ~s__s3__flags~7 : int;
    var ~s__s3__delay_buf_pop_ret~7 : int;
    var ~s__s3__tmp__cert_req~7 : int;
    var ~s__s3__tmp__new_compression~7 : int;
    var ~s__s3__tmp__reuse_message~7 : int;
    var ~s__s3__tmp__new_cipher~7 : int;
    var ~s__s3__tmp__new_cipher__algorithms~7 : int;
    var ~s__s3__tmp__next_state___0~7 : int;
    var ~s__s3__tmp__new_compression__id~7 : int;
    var ~s__session__cipher~7 : int;
    var ~s__session__compress_meth~7 : int;
    var ~buf~7 : int;
    var ~tmp~7 : int;
    var ~l~7 : int;
    var ~num1~7 : int;
    var ~cb~7 : int;
    var ~ret~7 : int;
    var ~new_state~7 : int;
    var ~state~7 : int;
    var ~skip~7 : int;
    var ~tmp___0~7 : int;
    var ~tmp___1~7 : int;
    var ~tmp___2~7 : int;
    var ~tmp___3~7 : int;
    var ~tmp___4~7 : int;
    var ~tmp___5~7 : int;
    var ~tmp___6~7 : int;
    var ~tmp___7~7 : int;
    var ~tmp___8~7 : int;
    var ~tmp___9~7 : int;
    var ~blastFlag~7 : int;
    var ~__cil_tmp55~7 : int;
    var ~__cil_tmp56~7 : int;
    var ~__cil_tmp57~7 : int;
    var ~__cil_tmp58~7 : int;
    var ~__cil_tmp59~7 : int;
    var ~__cil_tmp60~7 : int;
    var ~__cil_tmp61~7 : int;
    var ~__cil_tmp62~7 : int;
    var ~__cil_tmp63~7 : int;
    var ~__cil_tmp64~7 : int;
    var #t~nondet0 : int;
    var #t~nondet1 : int;
    var #t~nondet2 : int;
    var #t~nondet3 : int;
    var #t~nondet4 : int;
    var #t~nondet5 : int;
    var #t~nondet6 : int;
    var #t~nondet7 : int;
    var #t~nondet8 : int;
    var #t~nondet9 : int;
    var #t~nondet10 : int;
    var #t~nondet11 : int;
    var #t~nondet12 : int;
    var #t~nondet13 : int;
    var #t~nondet14 : int;
    var #t~nondet15 : int;
    var #t~nondet16 : int;
    var #t~nondet17 : int;
    var #t~nondet18 : int;
    var #t~nondet19 : int;
    var #t~nondet20 : int;
    var #t~nondet21 : int;
    var #t~nondet22 : int;
    var #t~nondet23 : int;
    var #t~nondet24 : int;
    var #t~nondet25 : int;
    var #t~nondet26 : int;
    var #t~nondet27 : int;
    var #t~post28 : int;
    var #t~post29 : int;
    var #t~nondet30 : int;
    var #t~post31 : int;
    var #t~nondet32 : int;
    var #t~nondet33 : int;
    var #t~nondet34 : int;
    var #t~nondet35 : int;
    var #t~nondet36 : int;
    var #t~nondet37 : int;
    var #t~nondet38 : int;
    var #t~nondet39 : int;
    var #t~nondet40 : int;
    var #t~nondet41 : int;
    var #t~nondet42 : int;
    var #t~nondet43 : int;
    var #t~post44 : int;
    var #t~post45 : int;
    var #t~nondet46 : int;
    var #t~post47 : int;

    ~initial_state := #in~initial_state;
    ~s__info_callback~7 := #t~nondet0;
    havoc #t~nondet0;
    ~s__in_handshake~7 := #t~nondet1;
    havoc #t~nondet1;
    havoc ~s__state~7;
    havoc ~s__new_session~7;
    havoc ~s__server~7;
    ~s__version~7 := #t~nondet2;
    havoc #t~nondet2;
    havoc ~s__type~7;
    havoc ~s__init_num~7;
    ~s__bbio~7 := #t~nondet3;
    havoc #t~nondet3;
    ~s__wbio~7 := #t~nondet4;
    havoc #t~nondet4;
    ~s__hit~7 := #t~nondet5;
    havoc #t~nondet5;
    havoc ~s__rwstate~7;
    havoc ~s__init_buf___0~7;
    ~s__debug~7 := #t~nondet6;
    havoc #t~nondet6;
    havoc ~s__shutdown~7;
    ~s__ctx__info_callback~7 := #t~nondet7;
    havoc #t~nondet7;
    ~s__ctx__stats__sess_connect_renegotiate~7 := #t~nondet8;
    havoc #t~nondet8;
    ~s__ctx__stats__sess_connect~7 := #t~nondet9;
    havoc #t~nondet9;
    ~s__ctx__stats__sess_hit~7 := #t~nondet10;
    havoc #t~nondet10;
    ~s__ctx__stats__sess_connect_good~7 := #t~nondet11;
    havoc #t~nondet11;
    havoc ~s__s3__change_cipher_spec~7;
    havoc ~s__s3__flags~7;
    havoc ~s__s3__delay_buf_pop_ret~7;
    ~s__s3__tmp__cert_req~7 := #t~nondet12;
    havoc #t~nondet12;
    ~s__s3__tmp__new_compression~7 := #t~nondet13;
    havoc #t~nondet13;
    ~s__s3__tmp__reuse_message~7 := #t~nondet14;
    havoc #t~nondet14;
    ~s__s3__tmp__new_cipher~7 := #t~nondet15;
    havoc #t~nondet15;
    ~s__s3__tmp__new_cipher__algorithms~7 := #t~nondet16;
    havoc #t~nondet16;
    havoc ~s__s3__tmp__next_state___0~7;
    ~s__s3__tmp__new_compression__id~7 := #t~nondet17;
    havoc #t~nondet17;
    havoc ~s__session__cipher~7;
    havoc ~s__session__compress_meth~7;
    havoc ~buf~7;
    havoc ~tmp~7;
    havoc ~l~7;
    havoc ~num1~7;
    havoc ~cb~7;
    havoc ~ret~7;
    havoc ~new_state~7;
    havoc ~state~7;
    havoc ~skip~7;
    havoc ~tmp___0~7;
    ~tmp___1~7 := #t~nondet18;
    havoc #t~nondet18;
    ~tmp___2~7 := #t~nondet19;
    havoc #t~nondet19;
    ~tmp___3~7 := #t~nondet20;
    havoc #t~nondet20;
    ~tmp___4~7 := #t~nondet21;
    havoc #t~nondet21;
    ~tmp___5~7 := #t~nondet22;
    havoc #t~nondet22;
    ~tmp___6~7 := #t~nondet23;
    havoc #t~nondet23;
    ~tmp___7~7 := #t~nondet24;
    havoc #t~nondet24;
    ~tmp___8~7 := #t~nondet25;
    havoc #t~nondet25;
    ~tmp___9~7 := #t~nondet26;
    havoc #t~nondet26;
    havoc ~blastFlag~7;
    havoc ~__cil_tmp55~7;
    havoc ~__cil_tmp56~7;
    havoc ~__cil_tmp57~7;
    havoc ~__cil_tmp58~7;
    havoc ~__cil_tmp59~7;
    havoc ~__cil_tmp60~7;
    havoc ~__cil_tmp61~7;
    havoc ~__cil_tmp62~7;
    havoc ~__cil_tmp63~7;
    havoc ~__cil_tmp64~7;
    ~s__state~7 := ~initial_state;
    ~blastFlag~7 := 0;
    ~tmp~7 := #t~nondet27;
    havoc #t~nondet27;
    ~cb~7 := 0;
    ~ret~7 := -1;
    ~skip~7 := 0;
    ~tmp___0~7 := 0;
    if (~s__info_callback~7 != 0) {
        ~cb~7 := ~s__info_callback~7;
    } else if (~s__ctx__info_callback~7 != 0) {
        ~cb~7 := ~s__ctx__info_callback~7;
    }
    #t~post28 := ~s__in_handshake~7;
    ~s__in_handshake~7 := #t~post28 + 1;
    havoc #t~post28;
    if (~tmp___1~7 - 12288 != 0) {
        if (~tmp___2~7 - 16384 != 0) {
        }
    }
    while (true)
    {
        if (!true) {
            break;
        }
      while_0_continue:
        ~state~7 := ~s__state~7;
        if (~s__state~7 == 12292) {
            goto switch_1_12292;
        } else if (~s__state~7 == 16384) {
            goto switch_1_16384;
        } else if (~s__state~7 == 4096) {
            goto switch_1_4096;
        } else if (~s__state~7 == 20480) {
            goto switch_1_20480;
        } else if (~s__state~7 == 4099) {
            goto switch_1_4099;
        } else if (~s__state~7 == 4368) {
            goto switch_1_4368;
        } else if (~s__state~7 == 4369) {
            goto switch_1_4369;
        } else if (~s__state~7 == 4384) {
            goto switch_1_4384;
        } else if (~s__state~7 == 4385) {
            goto switch_1_4385;
        } else if (~s__state~7 == 4400) {
            goto switch_1_4400;
        } else if (~s__state~7 == 4401) {
            goto switch_1_4401;
        } else if (~s__state~7 == 4416) {
            goto switch_1_4416;
        } else if (~s__state~7 == 4417) {
            goto switch_1_4417;
        } else if (~s__state~7 == 4432) {
            goto switch_1_4432;
        } else if (~s__state~7 == 4433) {
            goto switch_1_4433;
        } else if (~s__state~7 == 4448) {
            goto switch_1_4448;
        } else if (~s__state~7 == 4449) {
            goto switch_1_4449;
        } else if (~s__state~7 == 4464) {
            goto switch_1_4464;
        } else if (~s__state~7 == 4465) {
            goto switch_1_4465;
        } else if (~s__state~7 == 4466) {
            goto switch_1_4466;
        } else if (~s__state~7 == 4467) {
            goto switch_1_4467;
        } else if (~s__state~7 == 4480) {
            goto switch_1_4480;
        } else if (~s__state~7 == 4481) {
            goto switch_1_4481;
        } else if (~s__state~7 == 4496) {
            goto switch_1_4496;
        } else if (~s__state~7 == 4497) {
            goto switch_1_4497;
        } else if (~s__state~7 == 4512) {
            goto switch_1_4512;
        } else if (~s__state~7 == 4513) {
            goto switch_1_4513;
        } else if (~s__state~7 == 4528) {
            goto switch_1_4528;
        } else if (~s__state~7 == 4529) {
            goto switch_1_4529;
        } else if (~s__state~7 == 4560) {
            goto switch_1_4560;
        } else if (~s__state~7 == 4561) {
            goto switch_1_4561;
        } else if (~s__state~7 == 4352) {
            goto switch_1_4352;
        } else if (~s__state~7 == 3) {
            goto switch_1_3;
        } else {
            goto switch_1_default;
            if (false) {
              switch_1_12292:
                ~s__new_session~7 := 1;
                ~s__state~7 := 4096;
                #t~post29 := ~s__ctx__stats__sess_connect_renegotiate~7;
                ~s__ctx__stats__sess_connect_renegotiate~7 := #t~post29 + 1;
                havoc #t~post29;
              switch_1_16384:
              switch_1_4096:
              switch_1_20480:
              switch_1_4099:
                ~s__server~7 := 0;
                if (~cb~7 != 0) {
                }
                ~__cil_tmp55~7 := ~s__version~7 - 65280;
                if (~__cil_tmp55~7 != 768) {
                    ~ret~7 := -1;
                    goto end;
                }
                ~s__type~7 := 4096;
                if (~s__init_buf___0~7 == 0) {
                    ~buf~7 := #t~nondet30;
                    havoc #t~nondet30;
                    if (~buf~7 == 0) {
                        ~ret~7 := -1;
                        goto end;
                    }
                    if (!(~tmp___3~7 != 0)) {
                        ~ret~7 := -1;
                        goto end;
                    }
                    ~s__init_buf___0~7 := ~buf~7;
                }
                if (!(~tmp___4~7 != 0)) {
                    ~ret~7 := -1;
                    goto end;
                }
                if (!(~tmp___5~7 != 0)) {
                    ~ret~7 := -1;
                    goto end;
                }
                ~s__state~7 := 4368;
                #t~post31 := ~s__ctx__stats__sess_connect~7;
                ~s__ctx__stats__sess_connect~7 := #t~post31 + 1;
                havoc #t~post31;
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4368:
              switch_1_4369:
                ~s__shutdown~7 := 0;
                ~ret~7 := #t~nondet32;
                havoc #t~nondet32;
                if (~blastFlag~7 == 0) {
                    ~blastFlag~7 := 1;
                }
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~s__state~7 := 4384;
                ~s__init_num~7 := 0;
                if (~s__bbio~7 != ~s__wbio~7) {
                }
                goto switch_1_break;
              switch_1_4384:
              switch_1_4385:
                ~ret~7 := #t~nondet33;
                havoc #t~nondet33;
                if (~blastFlag~7 == 1) {
                    ~blastFlag~7 := 2;
                }
                if (~ret~7 <= 0) {
                    goto end;
                }
                if (~s__hit~7 != 0) {
                    ~s__state~7 := 4560;
                } else {
                    ~s__state~7 := 4400;
                }
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4400:
              switch_1_4401:
                if (~s__s3__tmp__new_cipher__algorithms~7 - 256 != 0) {
                    ~skip~7 := 1;
                } else {
                    ~ret~7 := #t~nondet34;
                    havoc #t~nondet34;
                    if (~blastFlag~7 == 2) {
                        ~blastFlag~7 := 3;
                    }
                    if (~ret~7 <= 0) {
                        goto end;
                    }
                }
                ~s__state~7 := 4416;
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4416:
              switch_1_4417:
                ~ret~7 := #t~nondet35;
                havoc #t~nondet35;
                if (~blastFlag~7 == 3) {
                    ~blastFlag~7 := 4;
                }
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~s__state~7 := 4432;
                ~s__init_num~7 := 0;
                if (!(~tmp___6~7 != 0)) {
                    ~ret~7 := -1;
                    goto end;
                }
                goto switch_1_break;
              switch_1_4432:
              switch_1_4433:
                ~ret~7 := #t~nondet36;
                havoc #t~nondet36;
                if (~blastFlag~7 == 5) {
                    goto ERROR;
                }
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~s__state~7 := 4448;
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4448:
              switch_1_4449:
                ~ret~7 := #t~nondet37;
                havoc #t~nondet37;
                if (~blastFlag~7 == 4) {
                    ~blastFlag~7 := 5;
                }
                if (~ret~7 <= 0) {
                    goto end;
                }
                if (~s__s3__tmp__cert_req~7 != 0) {
                    ~s__state~7 := 4464;
                } else {
                    ~s__state~7 := 4480;
                }
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4464:
              switch_1_4465:
              switch_1_4466:
              switch_1_4467:
                ~ret~7 := #t~nondet38;
                havoc #t~nondet38;
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~s__state~7 := 4480;
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4480:
              switch_1_4481:
                ~ret~7 := #t~nondet39;
                havoc #t~nondet39;
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~l~7 := ~s__s3__tmp__new_cipher__algorithms~7;
                if (~s__s3__tmp__cert_req~7 == 1) {
                    ~s__state~7 := 4496;
                } else {
                    ~s__state~7 := 4512;
                    ~s__s3__change_cipher_spec~7 := 0;
                }
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4496:
              switch_1_4497:
                ~ret~7 := #t~nondet40;
                havoc #t~nondet40;
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~s__state~7 := 4512;
                ~s__init_num~7 := 0;
                ~s__s3__change_cipher_spec~7 := 0;
                goto switch_1_break;
              switch_1_4512:
              switch_1_4513:
                ~ret~7 := #t~nondet41;
                havoc #t~nondet41;
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~s__state~7 := 4528;
                ~s__init_num~7 := 0;
                ~s__session__cipher~7 := ~s__s3__tmp__new_cipher~7;
                if (~s__s3__tmp__new_compression~7 == 0) {
                    ~s__session__compress_meth~7 := 0;
                } else {
                    ~s__session__compress_meth~7 := ~s__s3__tmp__new_compression__id~7;
                }
                if (!(~tmp___7~7 != 0)) {
                    ~ret~7 := -1;
                    goto end;
                }
                if (!(~tmp___8~7 != 0)) {
                    ~ret~7 := -1;
                    goto end;
                }
                goto switch_1_break;
              switch_1_4528:
              switch_1_4529:
                ~ret~7 := #t~nondet42;
                havoc #t~nondet42;
                if (~ret~7 <= 0) {
                    goto end;
                }
                ~s__state~7 := 4352;
                ~__cil_tmp56~7 := ~s__s3__flags~7;
                ~__cil_tmp57~7 := ~__cil_tmp56~7 + 5;
                ~s__s3__flags~7 := ~__cil_tmp57~7;
                if (~s__hit~7 != 0) {
                    ~s__s3__tmp__next_state___0~7 := 3;
                    ~__cil_tmp58~7 := ~s__s3__flags~7;
                    if (~__cil_tmp58~7 - 2 != 0) {
                        ~s__state~7 := 3;
                        ~__cil_tmp59~7 := ~s__s3__flags~7;
                        ~__cil_tmp60~7 := ~__cil_tmp59~7 + 4;
                        ~s__s3__flags~7 := ~__cil_tmp60~7;
                        ~s__s3__delay_buf_pop_ret~7 := 0;
                    }
                } else {
                    ~s__s3__tmp__next_state___0~7 := 4560;
                }
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4560:
              switch_1_4561:
                ~ret~7 := #t~nondet43;
                havoc #t~nondet43;
                if (~ret~7 <= 0) {
                    goto end;
                }
                if (~s__hit~7 != 0) {
                    ~s__state~7 := 4512;
                } else {
                    ~s__state~7 := 3;
                }
                ~s__init_num~7 := 0;
                goto switch_1_break;
              switch_1_4352:
                ~__cil_tmp61~7 := ~num1~7;
                if (~__cil_tmp61~7 > 0) {
                    ~s__rwstate~7 := 2;
                    ~num1~7 := ~tmp___9~7;
                    ~__cil_tmp62~7 := ~num1~7;
                    if (~__cil_tmp62~7 <= 0) {
                        ~ret~7 := -1;
                        goto end;
                    }
                    ~s__rwstate~7 := 1;
                }
                ~s__state~7 := ~s__s3__tmp__next_state___0~7;
                goto switch_1_break;
              switch_1_3:
                if (~s__init_buf___0~7 != 0) {
                    ~s__init_buf___0~7 := 0;
                }
                ~__cil_tmp63~7 := ~s__s3__flags~7;
                ~__cil_tmp64~7 := ~__cil_tmp63~7 - 4;
                if (!(~__cil_tmp64~7 != 0)) {
                }
                ~s__init_num~7 := 0;
                ~s__new_session~7 := 0;
                if (~s__hit~7 != 0) {
                    #t~post44 := ~s__ctx__stats__sess_hit~7;
                    ~s__ctx__stats__sess_hit~7 := #t~post44 + 1;
                    havoc #t~post44;
                }
                ~ret~7 := 1;
                #t~post45 := ~s__ctx__stats__sess_connect_good~7;
                ~s__ctx__stats__sess_connect_good~7 := #t~post45 + 1;
                havoc #t~post45;
                if (~cb~7 != 0) {
                }
                goto end;
              switch_1_default:
                ~ret~7 := -1;
                goto end;
            } else {
              switch_1_break:
            }
        }
        if (!(~s__s3__tmp__reuse_message~7 != 0)) {
            if (!(~skip~7 != 0)) {
                if (~s__debug~7 != 0) {
                    ~ret~7 := #t~nondet46;
                    havoc #t~nondet46;
                    if (~ret~7 <= 0) {
                        goto end;
                    }
                }
                if (~cb~7 != 0) {
                    if (~s__state~7 != ~state~7) {
                        ~new_state~7 := ~s__state~7;
                        ~s__state~7 := ~state~7;
                        ~s__state~7 := ~new_state~7;
                    }
                }
            }
        }
        ~skip~7 := 0;
    }
  while_0_break:
  end:
    #t~post47 := ~s__in_handshake~7;
    ~s__in_handshake~7 := #t~post47 - 1;
    havoc #t~post47;
    if (~cb~7 != 0) {
    }
    #res := ~ret~7;
    return;
  ERROR:
    if (*) {
        assert false;
    }
//    call __VERIFIER_error();
    #res := -1;
    return;
}


procedure ssl3_connect(#in~initial_state : int) returns (#res : int);
    modifies ;