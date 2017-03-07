implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~ret50 : int;
    var main_~s~174 : int;
    var main_~tmp~174 : int;
    var ssl3_accept_#in~initial_state : int;
    var ssl3_accept_#res : int;
    var ssl3_accept_#t~nondet0 : int;
    var ssl3_accept_#t~nondet1 : int;
    var ssl3_accept_#t~nondet2 : int;
    var ssl3_accept_#t~nondet3 : int;
    var ssl3_accept_#t~nondet4 : int;
    var ssl3_accept_#t~nondet5 : int;
    var ssl3_accept_#t~nondet6 : int;
    var ssl3_accept_#t~nondet7 : int;
    var ssl3_accept_#t~nondet8 : int;
    var ssl3_accept_#t~nondet9 : int;
    var ssl3_accept_#t~nondet10 : int;
    var ssl3_accept_#t~nondet11 : int;
    var ssl3_accept_#t~nondet12 : int;
    var ssl3_accept_#t~nondet13 : int;
    var ssl3_accept_#t~nondet14 : int;
    var ssl3_accept_#t~nondet15 : int;
    var ssl3_accept_#t~nondet16 : int;
    var ssl3_accept_#t~nondet17 : int;
    var ssl3_accept_#t~nondet18 : int;
    var ssl3_accept_#t~nondet19 : int;
    var ssl3_accept_#t~nondet20 : int;
    var ssl3_accept_#t~nondet21 : int;
    var ssl3_accept_#t~nondet22 : int;
    var ssl3_accept_#t~post23 : int;
    var ssl3_accept_#t~nondet24 : int;
    var ssl3_accept_#t~nondet25 : int;
    var ssl3_accept_#t~nondet26 : int;
    var ssl3_accept_#t~post27 : int;
    var ssl3_accept_#t~post28 : int;
    var ssl3_accept_#t~nondet29 : int;
    var ssl3_accept_#t~nondet30 : int;
    var ssl3_accept_#t~nondet31 : int;
    var ssl3_accept_#t~nondet32 : int;
    var ssl3_accept_#t~nondet33 : int;
    var ssl3_accept_#t~nondet34 : int;
    var ssl3_accept_#t~nondet35 : int;
    var ssl3_accept_#t~nondet36 : int;
    var ssl3_accept_#t~nondet37 : int;
    var ssl3_accept_#t~nondet38 : int;
    var ssl3_accept_#t~nondet39 : int;
    var ssl3_accept_#t~nondet40 : int;
    var ssl3_accept_#t~nondet41 : int;
    var ssl3_accept_#t~nondet42 : int;
    var ssl3_accept_#t~nondet43 : int;
    var ssl3_accept_#t~nondet44 : int;
    var ssl3_accept_#t~nondet45 : int;
    var ssl3_accept_#t~nondet46 : int;
    var ssl3_accept_#t~post47 : int;
    var ssl3_accept_#t~nondet48 : int;
    var ssl3_accept_#t~post49 : int;
    var ssl3_accept_~initial_state : int;
    var ssl3_accept_~s__info_callback~6 : int;
    var ssl3_accept_~s__in_handshake~6 : int;
    var ssl3_accept_~s__state~6 : int;
    var ssl3_accept_~s__new_session~6 : int;
    var ssl3_accept_~s__server~6 : int;
    var ssl3_accept_~s__version~6 : int;
    var ssl3_accept_~s__type~6 : int;
    var ssl3_accept_~s__init_num~6 : int;
    var ssl3_accept_~s__hit~6 : int;
    var ssl3_accept_~s__rwstate~6 : int;
    var ssl3_accept_~s__init_buf___0~6 : int;
    var ssl3_accept_~s__debug~6 : int;
    var ssl3_accept_~s__shutdown~6 : int;
    var ssl3_accept_~s__cert~6 : int;
    var ssl3_accept_~s__options~6 : int;
    var ssl3_accept_~s__verify_mode~6 : int;
    var ssl3_accept_~s__session__peer~6 : int;
    var ssl3_accept_~s__cert__pkeys__AT0__privatekey~6 : int;
    var ssl3_accept_~s__ctx__info_callback~6 : int;
    var ssl3_accept_~s__ctx__stats__sess_accept_renegotiate~6 : int;
    var ssl3_accept_~s__ctx__stats__sess_accept~6 : int;
    var ssl3_accept_~s__ctx__stats__sess_accept_good~6 : int;
    var ssl3_accept_~s__s3__tmp__cert_request~6 : int;
    var ssl3_accept_~s__s3__tmp__reuse_message~6 : int;
    var ssl3_accept_~s__s3__tmp__use_rsa_tmp~6 : int;
    var ssl3_accept_~s__s3__tmp__new_cipher~6 : int;
    var ssl3_accept_~s__s3__tmp__new_cipher__algorithms~6 : int;
    var ssl3_accept_~s__s3__tmp__next_state___0~6 : int;
    var ssl3_accept_~s__s3__tmp__new_cipher__algo_strength~6 : int;
    var ssl3_accept_~s__session__cipher~6 : int;
    var ssl3_accept_~buf~6 : int;
    var ssl3_accept_~l~6 : int;
    var ssl3_accept_~Time~6 : int;
    var ssl3_accept_~tmp~6 : int;
    var ssl3_accept_~cb~6 : int;
    var ssl3_accept_~num1~6 : int;
    var ssl3_accept_~ret~6 : int;
    var ssl3_accept_~new_state~6 : int;
    var ssl3_accept_~state~6 : int;
    var ssl3_accept_~skip~6 : int;
    var ssl3_accept_~got_new_session~6 : int;
    var ssl3_accept_~tmp___1~6 : int;
    var ssl3_accept_~tmp___2~6 : int;
    var ssl3_accept_~tmp___3~6 : int;
    var ssl3_accept_~tmp___4~6 : int;
    var ssl3_accept_~tmp___5~6 : int;
    var ssl3_accept_~tmp___6~6 : int;
    var ssl3_accept_~tmp___7~6 : int;
    var ssl3_accept_~tmp___8~6 : int;
    var ssl3_accept_~tmp___9~6 : int;
    var ssl3_accept_~tmp___10~6 : int;
    var ssl3_accept_~blastFlag~6 : int;
    var ssl3_accept_~__cil_tmp55~6 : int;
    var ssl3_accept_~__cil_tmp56~6 : int;
    var ssl3_accept_~__cil_tmp57~6 : int;
    var ssl3_accept_~__cil_tmp58~6 : int;
    var ssl3_accept_~__cil_tmp59~6 : int;
    var ssl3_accept_~__cil_tmp60~6 : int;
    var ssl3_accept_~__cil_tmp61~6 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~ret50, main_~s~174, main_~tmp~174;
    havoc main_~s~174;
    havoc main_~tmp~174;
    main_~s~174 := 8464;
    ssl3_accept_#in~initial_state := main_~s~174;
    havoc ssl3_accept_#res;
    havoc ssl3_accept_#t~nondet0, ssl3_accept_#t~nondet1, ssl3_accept_#t~nondet2, ssl3_accept_#t~nondet3, ssl3_accept_#t~nondet4, ssl3_accept_#t~nondet5, ssl3_accept_#t~nondet6, ssl3_accept_#t~nondet7, ssl3_accept_#t~nondet8, ssl3_accept_#t~nondet9, ssl3_accept_#t~nondet10, ssl3_accept_#t~nondet11, ssl3_accept_#t~nondet12, ssl3_accept_#t~nondet13, ssl3_accept_#t~nondet14, ssl3_accept_#t~nondet15, ssl3_accept_#t~nondet16, ssl3_accept_#t~nondet17, ssl3_accept_#t~nondet18, ssl3_accept_#t~nondet19, ssl3_accept_#t~nondet20, ssl3_accept_#t~nondet21, ssl3_accept_#t~nondet22, ssl3_accept_#t~post23, ssl3_accept_#t~nondet24, ssl3_accept_#t~nondet25, ssl3_accept_#t~nondet26, ssl3_accept_#t~post27, ssl3_accept_#t~post28, ssl3_accept_#t~nondet29, ssl3_accept_#t~nondet30, ssl3_accept_#t~nondet31, ssl3_accept_#t~nondet32, ssl3_accept_#t~nondet33, ssl3_accept_#t~nondet34, ssl3_accept_#t~nondet35, ssl3_accept_#t~nondet36, ssl3_accept_#t~nondet37, ssl3_accept_#t~nondet38, ssl3_accept_#t~nondet39, ssl3_accept_#t~nondet40, ssl3_accept_#t~nondet41, ssl3_accept_#t~nondet42, ssl3_accept_#t~nondet43, ssl3_accept_#t~nondet44, ssl3_accept_#t~nondet45, ssl3_accept_#t~nondet46, ssl3_accept_#t~post47, ssl3_accept_#t~nondet48, ssl3_accept_#t~post49, ssl3_accept_~initial_state, ssl3_accept_~s__info_callback~6, ssl3_accept_~s__in_handshake~6, ssl3_accept_~s__state~6, ssl3_accept_~s__new_session~6, ssl3_accept_~s__server~6, ssl3_accept_~s__version~6, ssl3_accept_~s__type~6, ssl3_accept_~s__init_num~6, ssl3_accept_~s__hit~6, ssl3_accept_~s__rwstate~6, ssl3_accept_~s__init_buf___0~6, ssl3_accept_~s__debug~6, ssl3_accept_~s__shutdown~6, ssl3_accept_~s__cert~6, ssl3_accept_~s__options~6, ssl3_accept_~s__verify_mode~6, ssl3_accept_~s__session__peer~6, ssl3_accept_~s__cert__pkeys__AT0__privatekey~6, ssl3_accept_~s__ctx__info_callback~6, ssl3_accept_~s__ctx__stats__sess_accept_renegotiate~6, ssl3_accept_~s__ctx__stats__sess_accept~6, ssl3_accept_~s__ctx__stats__sess_accept_good~6, ssl3_accept_~s__s3__tmp__cert_request~6, ssl3_accept_~s__s3__tmp__reuse_message~6, ssl3_accept_~s__s3__tmp__use_rsa_tmp~6, ssl3_accept_~s__s3__tmp__new_cipher~6, ssl3_accept_~s__s3__tmp__new_cipher__algorithms~6, ssl3_accept_~s__s3__tmp__next_state___0~6, ssl3_accept_~s__s3__tmp__new_cipher__algo_strength~6, ssl3_accept_~s__session__cipher~6, ssl3_accept_~buf~6, ssl3_accept_~l~6, ssl3_accept_~Time~6, ssl3_accept_~tmp~6, ssl3_accept_~cb~6, ssl3_accept_~num1~6, ssl3_accept_~ret~6, ssl3_accept_~new_state~6, ssl3_accept_~state~6, ssl3_accept_~skip~6, ssl3_accept_~got_new_session~6, ssl3_accept_~tmp___1~6, ssl3_accept_~tmp___2~6, ssl3_accept_~tmp___3~6, ssl3_accept_~tmp___4~6, ssl3_accept_~tmp___5~6, ssl3_accept_~tmp___6~6, ssl3_accept_~tmp___7~6, ssl3_accept_~tmp___8~6, ssl3_accept_~tmp___9~6, ssl3_accept_~tmp___10~6, ssl3_accept_~blastFlag~6, ssl3_accept_~__cil_tmp55~6, ssl3_accept_~__cil_tmp56~6, ssl3_accept_~__cil_tmp57~6, ssl3_accept_~__cil_tmp58~6, ssl3_accept_~__cil_tmp59~6, ssl3_accept_~__cil_tmp60~6, ssl3_accept_~__cil_tmp61~6;
    ssl3_accept_~initial_state := ssl3_accept_#in~initial_state;
    assume -2147483648 <= ssl3_accept_#t~nondet0 && ssl3_accept_#t~nondet0 <= 2147483647;
    ssl3_accept_~s__info_callback~6 := ssl3_accept_#t~nondet0;
    havoc ssl3_accept_#t~nondet0;
    assume -2147483648 <= ssl3_accept_#t~nondet1 && ssl3_accept_#t~nondet1 <= 2147483647;
    ssl3_accept_~s__in_handshake~6 := ssl3_accept_#t~nondet1;
    havoc ssl3_accept_#t~nondet1;
    havoc ssl3_accept_~s__state~6;
    havoc ssl3_accept_~s__new_session~6;
    havoc ssl3_accept_~s__server~6;
    assume -2147483648 <= ssl3_accept_#t~nondet2 && ssl3_accept_#t~nondet2 <= 2147483647;
    ssl3_accept_~s__version~6 := ssl3_accept_#t~nondet2;
    havoc ssl3_accept_#t~nondet2;
    havoc ssl3_accept_~s__type~6;
    havoc ssl3_accept_~s__init_num~6;
    assume -2147483648 <= ssl3_accept_#t~nondet3 && ssl3_accept_#t~nondet3 <= 2147483647;
    ssl3_accept_~s__hit~6 := ssl3_accept_#t~nondet3;
    havoc ssl3_accept_#t~nondet3;
    havoc ssl3_accept_~s__rwstate~6;
    havoc ssl3_accept_~s__init_buf___0~6;
    assume -2147483648 <= ssl3_accept_#t~nondet4 && ssl3_accept_#t~nondet4 <= 2147483647;
    ssl3_accept_~s__debug~6 := ssl3_accept_#t~nondet4;
    havoc ssl3_accept_#t~nondet4;
    havoc ssl3_accept_~s__shutdown~6;
    assume -2147483648 <= ssl3_accept_#t~nondet5 && ssl3_accept_#t~nondet5 <= 2147483647;
    ssl3_accept_~s__cert~6 := ssl3_accept_#t~nondet5;
    havoc ssl3_accept_#t~nondet5;
    assume -2147483648 <= ssl3_accept_#t~nondet6 && ssl3_accept_#t~nondet6 <= 2147483647;
    ssl3_accept_~s__options~6 := ssl3_accept_#t~nondet6;
    havoc ssl3_accept_#t~nondet6;
    assume -2147483648 <= ssl3_accept_#t~nondet7 && ssl3_accept_#t~nondet7 <= 2147483647;
    ssl3_accept_~s__verify_mode~6 := ssl3_accept_#t~nondet7;
    havoc ssl3_accept_#t~nondet7;
    assume -2147483648 <= ssl3_accept_#t~nondet8 && ssl3_accept_#t~nondet8 <= 2147483647;
    ssl3_accept_~s__session__peer~6 := ssl3_accept_#t~nondet8;
    havoc ssl3_accept_#t~nondet8;
    assume -2147483648 <= ssl3_accept_#t~nondet9 && ssl3_accept_#t~nondet9 <= 2147483647;
    ssl3_accept_~s__cert__pkeys__AT0__privatekey~6 := ssl3_accept_#t~nondet9;
    havoc ssl3_accept_#t~nondet9;
    assume -2147483648 <= ssl3_accept_#t~nondet10 && ssl3_accept_#t~nondet10 <= 2147483647;
    ssl3_accept_~s__ctx__info_callback~6 := ssl3_accept_#t~nondet10;
    havoc ssl3_accept_#t~nondet10;
    assume -2147483648 <= ssl3_accept_#t~nondet11 && ssl3_accept_#t~nondet11 <= 2147483647;
    ssl3_accept_~s__ctx__stats__sess_accept_renegotiate~6 := ssl3_accept_#t~nondet11;
    havoc ssl3_accept_#t~nondet11;
    assume -2147483648 <= ssl3_accept_#t~nondet12 && ssl3_accept_#t~nondet12 <= 2147483647;
    ssl3_accept_~s__ctx__stats__sess_accept~6 := ssl3_accept_#t~nondet12;
    havoc ssl3_accept_#t~nondet12;
    assume -2147483648 <= ssl3_accept_#t~nondet13 && ssl3_accept_#t~nondet13 <= 2147483647;
    ssl3_accept_~s__ctx__stats__sess_accept_good~6 := ssl3_accept_#t~nondet13;
    havoc ssl3_accept_#t~nondet13;
    havoc ssl3_accept_~s__s3__tmp__cert_request~6;
    assume -2147483648 <= ssl3_accept_#t~nondet14 && ssl3_accept_#t~nondet14 <= 2147483647;
    ssl3_accept_~s__s3__tmp__reuse_message~6 := ssl3_accept_#t~nondet14;
    havoc ssl3_accept_#t~nondet14;
    havoc ssl3_accept_~s__s3__tmp__use_rsa_tmp~6;
    assume -2147483648 <= ssl3_accept_#t~nondet15 && ssl3_accept_#t~nondet15 <= 2147483647;
    ssl3_accept_~s__s3__tmp__new_cipher~6 := ssl3_accept_#t~nondet15;
    havoc ssl3_accept_#t~nondet15;
    assume -2147483648 <= ssl3_accept_#t~nondet16 && ssl3_accept_#t~nondet16 <= 2147483647;
    ssl3_accept_~s__s3__tmp__new_cipher__algorithms~6 := ssl3_accept_#t~nondet16;
    havoc ssl3_accept_#t~nondet16;
    havoc ssl3_accept_~s__s3__tmp__next_state___0~6;
    assume -2147483648 <= ssl3_accept_#t~nondet17 && ssl3_accept_#t~nondet17 <= 2147483647;
    ssl3_accept_~s__s3__tmp__new_cipher__algo_strength~6 := ssl3_accept_#t~nondet17;
    havoc ssl3_accept_#t~nondet17;
    havoc ssl3_accept_~s__session__cipher~6;
    assume -2147483648 <= ssl3_accept_#t~nondet18 && ssl3_accept_#t~nondet18 <= 2147483647;
    ssl3_accept_~buf~6 := ssl3_accept_#t~nondet18;
    havoc ssl3_accept_#t~nondet18;
    havoc ssl3_accept_~l~6;
    havoc ssl3_accept_~Time~6;
    assume -9223372036854775808 <= ssl3_accept_#t~nondet19 && ssl3_accept_#t~nondet19 <= 9223372036854775807;
    ssl3_accept_~tmp~6 := ssl3_accept_#t~nondet19;
    havoc ssl3_accept_#t~nondet19;
    havoc ssl3_accept_~cb~6;
    havoc ssl3_accept_~num1~6;
    havoc ssl3_accept_~ret~6;
    havoc ssl3_accept_~new_state~6;
    havoc ssl3_accept_~state~6;
    havoc ssl3_accept_~skip~6;
    havoc ssl3_accept_~got_new_session~6;
    assume -2147483648 <= ssl3_accept_#t~nondet20 && ssl3_accept_#t~nondet20 <= 2147483647;
    ssl3_accept_~tmp___1~6 := ssl3_accept_#t~nondet20;
    havoc ssl3_accept_#t~nondet20;
    assume -2147483648 <= ssl3_accept_#t~nondet21 && ssl3_accept_#t~nondet21 <= 2147483647;
    ssl3_accept_~tmp___2~6 := ssl3_accept_#t~nondet21;
    havoc ssl3_accept_#t~nondet21;
    havoc ssl3_accept_~tmp___3~6;
    havoc ssl3_accept_~tmp___4~6;
    havoc ssl3_accept_~tmp___5~6;
    havoc ssl3_accept_~tmp___6~6;
    havoc ssl3_accept_~tmp___7~6;
    assume -9223372036854775808 <= ssl3_accept_#t~nondet22 && ssl3_accept_#t~nondet22 <= 9223372036854775807;
    ssl3_accept_~tmp___8~6 := ssl3_accept_#t~nondet22;
    havoc ssl3_accept_#t~nondet22;
    havoc ssl3_accept_~tmp___9~6;
    havoc ssl3_accept_~tmp___10~6;
    havoc ssl3_accept_~blastFlag~6;
    havoc ssl3_accept_~__cil_tmp55~6;
    havoc ssl3_accept_~__cil_tmp56~6;
    havoc ssl3_accept_~__cil_tmp57~6;
    havoc ssl3_accept_~__cil_tmp58~6;
    havoc ssl3_accept_~__cil_tmp59~6;
    havoc ssl3_accept_~__cil_tmp60~6;
    havoc ssl3_accept_~__cil_tmp61~6;
    ssl3_accept_~s__state~6 := ssl3_accept_~initial_state;
    ssl3_accept_~blastFlag~6 := 0;
    ssl3_accept_~Time~6 := ssl3_accept_~tmp~6;
    ssl3_accept_~cb~6 := 0;
    ssl3_accept_~ret~6 := -1;
    ssl3_accept_~skip~6 := 0;
    ssl3_accept_~got_new_session~6 := 0;
    assume ssl3_accept_~s__info_callback~6 != 0;
    ssl3_accept_~cb~6 := ssl3_accept_~s__info_callback~6;
    ssl3_accept_#t~post23 := ssl3_accept_~s__in_handshake~6;
    ssl3_accept_~s__in_handshake~6 := ssl3_accept_#t~post23 + 1;
    havoc ssl3_accept_#t~post23;
    assume !(ssl3_accept_~tmp___1~6 + 12288 != 0);
    assume !(ssl3_accept_~s__cert~6 == 0);
    goto loc1;
  loc1:
    assume true;
    assume !false;
    ssl3_accept_~state~6 := ssl3_accept_~s__state~6;
    assume !(ssl3_accept_~s__state~6 == 12292);
    assume !(ssl3_accept_~s__state~6 == 16384);
    assume !(ssl3_accept_~s__state~6 == 8192);
    assume !(ssl3_accept_~s__state~6 == 24576);
    assume !(ssl3_accept_~s__state~6 == 8195);
    assume !(ssl3_accept_~s__state~6 == 8480);
    assume !(ssl3_accept_~s__state~6 == 8481);
    assume !(ssl3_accept_~s__state~6 == 8482);
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume ssl3_accept_~s__state~6 == 8464;
    ssl3_accept_~s__shutdown~6 := 0;
    assume -2147483648 <= ssl3_accept_#t~nondet30 && ssl3_accept_#t~nondet30 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet30;
    havoc ssl3_accept_#t~nondet30;
    assume ssl3_accept_~blastFlag~6 == 0;
    ssl3_accept_~blastFlag~6 := 1;
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~got_new_session~6 := 1;
    ssl3_accept_~s__state~6 := 8496;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc2_1:
    assume !(ssl3_accept_~s__state~6 == 8464);
    assume !(ssl3_accept_~s__state~6 == 8465);
    assume !(ssl3_accept_~s__state~6 == 8466);
    goto loc4;
  loc3:
    assume !(ssl3_accept_~s__s3__tmp__reuse_message~6 == 0);
    ssl3_accept_~skip~6 := 0;
    goto loc1;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume ssl3_accept_~s__state~6 == 8496;
    assume -2147483648 <= ssl3_accept_#t~nondet31 && ssl3_accept_#t~nondet31 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet31;
    havoc ssl3_accept_#t~nondet31;
    assume ssl3_accept_~blastFlag~6 == 1;
    ssl3_accept_~blastFlag~6 := 2;
    assume !(ssl3_accept_~ret~6 <= 0);
    assume !(ssl3_accept_~s__hit~6 != 0);
    ssl3_accept_~s__state~6 := 8512;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc4_1:
    assume !(ssl3_accept_~s__state~6 == 8496);
    assume !(ssl3_accept_~s__state~6 == 8497);
    goto loc5;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume ssl3_accept_~s__state~6 == 8512;
    ssl3_accept_~__cil_tmp56~6 := ssl3_accept_~s__s3__tmp__new_cipher__algorithms~6;
    assume (ssl3_accept_~__cil_tmp56~6 + 256) % 18446744073709551616 != 0;
    ssl3_accept_~skip~6 := 1;
    ssl3_accept_~s__state~6 := 8528;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc5_1:
    assume !(ssl3_accept_~s__state~6 == 8512);
    assume !(ssl3_accept_~s__state~6 == 8513);
    goto loc6;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume ssl3_accept_~s__state~6 == 8528;
    ssl3_accept_~l~6 := ssl3_accept_~s__s3__tmp__new_cipher__algorithms~6;
    ssl3_accept_~__cil_tmp57~6 := ssl3_accept_~s__options~6;
    assume (ssl3_accept_~__cil_tmp57~6 + 2097152) % 18446744073709551616 != 0;
    ssl3_accept_~s__s3__tmp__use_rsa_tmp~6 := 1;
    assume ssl3_accept_~s__s3__tmp__use_rsa_tmp~6 != 0;
    assume -2147483648 <= ssl3_accept_#t~nondet34 && ssl3_accept_#t~nondet34 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet34;
    havoc ssl3_accept_#t~nondet34;
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~s__state~6 := 8544;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc6_1:
    assume !(ssl3_accept_~s__state~6 == 8528);
    assume !(ssl3_accept_~s__state~6 == 8529);
    goto loc7;
  loc7:
    goto loc7_0, loc7_1;
  loc7_0:
    assume ssl3_accept_~s__state~6 == 8544;
    assume ssl3_accept_~s__verify_mode~6 + 1 != 0;
    assume !(ssl3_accept_~s__session__peer~6 != 0);
    ssl3_accept_~__cil_tmp61~6 := ssl3_accept_~s__s3__tmp__new_cipher__algorithms~6;
    assume !((ssl3_accept_~__cil_tmp61~6 + 256) % 18446744073709551616 != 0);
    ssl3_accept_~s__s3__tmp__cert_request~6 := 1;
    assume -2147483648 <= ssl3_accept_#t~nondet35 && ssl3_accept_#t~nondet35 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet35;
    havoc ssl3_accept_#t~nondet35;
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~s__state~6 := 8448;
    ssl3_accept_~s__s3__tmp__next_state___0~6 := 8576;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc7_1:
    assume !(ssl3_accept_~s__state~6 == 8544);
    assume !(ssl3_accept_~s__state~6 == 8545);
    assume !(ssl3_accept_~s__state~6 == 8560);
    assume !(ssl3_accept_~s__state~6 == 8561);
    goto loc8;
  loc8:
    goto loc8_0, loc8_1;
  loc8_0:
    assume ssl3_accept_~s__state~6 == 8448;
    assume -2147483648 <= ssl3_accept_#t~nondet37 && ssl3_accept_#t~nondet37 <= 2147483647;
    ssl3_accept_~num1~6 := ssl3_accept_#t~nondet37;
    havoc ssl3_accept_#t~nondet37;
    assume !(ssl3_accept_~num1~6 > 0);
    ssl3_accept_~s__state~6 := ssl3_accept_~s__s3__tmp__next_state___0~6;
    goto loc3;
  loc8_1:
    assume !(ssl3_accept_~s__state~6 == 8448);
    goto loc9;
  loc9:
    goto loc9_0, loc9_1;
  loc9_0:
    assume ssl3_accept_~s__state~6 == 8576;
    assume -2147483648 <= ssl3_accept_#t~nondet38 && ssl3_accept_#t~nondet38 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet38;
    havoc ssl3_accept_#t~nondet38;
    assume !(ssl3_accept_~ret~6 <= 0);
    assume !(ssl3_accept_~ret~6 == 2);
    assume -2147483648 <= ssl3_accept_#t~nondet39 && ssl3_accept_#t~nondet39 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet39;
    havoc ssl3_accept_#t~nondet39;
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~s__init_num~6 := 0;
    ssl3_accept_~s__state~6 := 8592;
    goto loc3;
  loc9_1:
    assume !(ssl3_accept_~s__state~6 == 8576);
    assume !(ssl3_accept_~s__state~6 == 8577);
    goto loc10;
  loc10:
    goto loc10_0, loc10_1;
  loc10_0:
    assume ssl3_accept_~s__state~6 == 8592;
    assume -2147483648 <= ssl3_accept_#t~nondet40 && ssl3_accept_#t~nondet40 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet40;
    havoc ssl3_accept_#t~nondet40;
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~s__state~6 := 8608;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc10_1:
    assume !(ssl3_accept_~s__state~6 == 8592);
    assume !(ssl3_accept_~s__state~6 == 8593);
    goto loc11;
  loc11:
    goto loc11_0, loc11_1;
  loc11_0:
    assume ssl3_accept_~s__state~6 == 8608;
    assume -2147483648 <= ssl3_accept_#t~nondet41 && ssl3_accept_#t~nondet41 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet41;
    havoc ssl3_accept_#t~nondet41;
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~s__state~6 := 8640;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc11_1:
    assume !(ssl3_accept_~s__state~6 == 8608);
    assume !(ssl3_accept_~s__state~6 == 8609);
    goto loc12;
  loc12:
    goto loc12_0, loc12_1;
  loc12_0:
    assume ssl3_accept_~s__state~6 == 8640;
    assume -2147483648 <= ssl3_accept_#t~nondet42 && ssl3_accept_#t~nondet42 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet42;
    havoc ssl3_accept_#t~nondet42;
    goto loc13;
  loc12_1:
    assume !(ssl3_accept_~s__state~6 == 8640);
    assume !(ssl3_accept_~s__state~6 == 8641);
    goto loc14;
  loc13:
    goto loc13_0, loc13_1;
  loc13_0:
    assume ssl3_accept_~blastFlag~6 == 3;
    ssl3_accept_~blastFlag~6 := 4;
    goto loc15;
  loc13_1:
    assume !(ssl3_accept_~blastFlag~6 == 3);
    goto loc15;
  loc14:
    goto loc14_0, loc14_1;
  loc14_0:
    assume ssl3_accept_~s__state~6 == 8656;
    ssl3_accept_~s__session__cipher~6 := ssl3_accept_~s__s3__tmp__new_cipher~6;
    assume -2147483648 <= ssl3_accept_#t~nondet43 && ssl3_accept_#t~nondet43 <= 2147483647;
    ssl3_accept_~tmp___9~6 := ssl3_accept_#t~nondet43;
    havoc ssl3_accept_#t~nondet43;
    assume !(ssl3_accept_~tmp___9~6 == 0);
    assume -2147483648 <= ssl3_accept_#t~nondet44 && ssl3_accept_#t~nondet44 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet44;
    havoc ssl3_accept_#t~nondet44;
    goto loc16;
  loc14_1:
    assume !(ssl3_accept_~s__state~6 == 8656);
    assume !(ssl3_accept_~s__state~6 == 8657);
    assume ssl3_accept_~s__state~6 == 8672;
    assume -2147483648 <= ssl3_accept_#t~nondet46 && ssl3_accept_#t~nondet46 <= 2147483647;
    ssl3_accept_~ret~6 := ssl3_accept_#t~nondet46;
    havoc ssl3_accept_#t~nondet46;
    goto loc17;
  loc15:
    assume !(ssl3_accept_~ret~6 <= 0);
    assume !(ssl3_accept_~s__hit~6 != 0);
    ssl3_accept_~s__state~6 := 8656;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc16:
    goto loc16_0, loc16_1;
  loc16_0:
    assume ssl3_accept_~blastFlag~6 == 2;
    ssl3_accept_~blastFlag~6 := 3;
    goto loc18;
  loc16_1:
    assume !(ssl3_accept_~blastFlag~6 == 2);
    goto loc18;
  loc17:
    goto loc17_0, loc17_1;
  loc17_0:
    assume ssl3_accept_~blastFlag~6 == 4;
    ssl3_accept_~blastFlag~6 := 5;
    goto loc19;
  loc17_1:
    assume !(ssl3_accept_~blastFlag~6 == 4);
    goto loc20;
  loc18:
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~s__state~6 := 8672;
    ssl3_accept_~s__init_num~6 := 0;
    assume -2147483648 <= ssl3_accept_#t~nondet45 && ssl3_accept_#t~nondet45 <= 2147483647;
    ssl3_accept_~tmp___10~6 := ssl3_accept_#t~nondet45;
    havoc ssl3_accept_#t~nondet45;
    assume !(ssl3_accept_~tmp___10~6 == 0);
    goto loc3;
  loc19:
    assume !(ssl3_accept_~ret~6 <= 0);
    ssl3_accept_~s__state~6 := 8448;
    assume !(ssl3_accept_~s__hit~6 != 0);
    ssl3_accept_~s__s3__tmp__next_state___0~6 := 3;
    ssl3_accept_~s__init_num~6 := 0;
    goto loc3;
  loc20:
    goto loc20_0, loc20_1;
  loc20_0:
    assume ssl3_accept_~blastFlag~6 == 5;
    assume !false;
    goto loc21;
  loc20_1:
    assume !(ssl3_accept_~blastFlag~6 == 5);
    goto loc19;
  loc21:
    assert false;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

