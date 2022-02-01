function { :overapproximation "bitwiseOr" } ~bitwiseOr(in0 : int, in1 : int) returns (out : int);
implementation ULTIMATE.start() returns (){
    var main_#res : int;
    var main_#t~ret41 : int;
    var main_~__retres1~187 : int;
    var ssl3_connect_#res : int;
    var ssl3_connect_#t~nondet0 : int;
    var ssl3_connect_#t~nondet1 : int;
    var ssl3_connect_#t~nondet2 : int;
    var ssl3_connect_#t~nondet3 : int;
    var ssl3_connect_#t~nondet4 : int;
    var ssl3_connect_#t~nondet5 : int;
    var ssl3_connect_#t~nondet6 : int;
    var ssl3_connect_#t~nondet7 : int;
    var ssl3_connect_#t~nondet8 : int;
    var ssl3_connect_#t~nondet9 : int;
    var ssl3_connect_#t~nondet10 : int;
    var ssl3_connect_#t~nondet11 : int;
    var ssl3_connect_#t~nondet12 : int;
    var ssl3_connect_#t~nondet13 : int;
    var ssl3_connect_#t~nondet14 : int;
    var ssl3_connect_#t~nondet15 : int;
    var ssl3_connect_#t~nondet16 : int;
    var ssl3_connect_#t~nondet17 : int;
    var ssl3_connect_#t~nondet18 : int;
    var ssl3_connect_#t~nondet19 : int;
    var ssl3_connect_#t~nondet20 : int;
    var ssl3_connect_#t~nondet21 : int;
    var ssl3_connect_#t~nondet22 : int;
    var ssl3_connect_#t~nondet23 : int;
    var ssl3_connect_#t~nondet24 : int;
    var ssl3_connect_#t~nondet25 : int;
    var ssl3_connect_#t~nondet26 : int;
    var ssl3_connect_#t~nondet27 : int;
    var ssl3_connect_#t~nondet28 : int;
    var ssl3_connect_#t~nondet29 : int;
    var ssl3_connect_#t~nondet30 : int;
    var ssl3_connect_#t~nondet31 : int;
    var ssl3_connect_#t~nondet32 : int;
    var ssl3_connect_#t~nondet33 : int;
    var ssl3_connect_#t~nondet34 : int;
    var ssl3_connect_#t~nondet35 : int;
    var ssl3_connect_#t~nondet36 : int;
    var ssl3_connect_#t~nondet37 : int;
    var ssl3_connect_#t~nondet38 : int;
    var ssl3_connect_#t~nondet39 : int;
    var ssl3_connect_#t~nondet40 : int;
    var ssl3_connect_~s__info_callback~3 : int;
    var ssl3_connect_~s__in_handshake~3 : int;
    var ssl3_connect_~s__state~3 : int;
    var ssl3_connect_~s__new_session~3 : int;
    var ssl3_connect_~s__server~3 : int;
    var ssl3_connect_~s__version~3 : int;
    var ssl3_connect_~s__type~3 : int;
    var ssl3_connect_~s__init_num~3 : int;
    var ssl3_connect_~s__bbio~3 : int;
    var ssl3_connect_~s__wbio~3 : int;
    var ssl3_connect_~s__hit~3 : int;
    var ssl3_connect_~s__rwstate~3 : int;
    var ssl3_connect_~s__init_buf___0~3 : int;
    var ssl3_connect_~s__debug~3 : int;
    var ssl3_connect_~s__shutdown~3 : int;
    var ssl3_connect_~s__ctx__info_callback~3 : int;
    var ssl3_connect_~s__ctx__stats__sess_connect_renegotiate~3 : int;
    var ssl3_connect_~s__ctx__stats__sess_connect~3 : int;
    var ssl3_connect_~s__ctx__stats__sess_hit~3 : int;
    var ssl3_connect_~s__ctx__stats__sess_connect_good~3 : int;
    var ssl3_connect_~s__s3__change_cipher_spec~3 : int;
    var ssl3_connect_~s__s3__flags~3 : int;
    var ssl3_connect_~s__s3__delay_buf_pop_ret~3 : int;
    var ssl3_connect_~s__s3__tmp__cert_req~3 : int;
    var ssl3_connect_~s__s3__tmp__new_compression~3 : int;
    var ssl3_connect_~s__s3__tmp__reuse_message~3 : int;
    var ssl3_connect_~s__s3__tmp__new_cipher~3 : int;
    var ssl3_connect_~s__s3__tmp__new_cipher__algorithms~3 : int;
    var ssl3_connect_~s__s3__tmp__next_state___0~3 : int;
    var ssl3_connect_~s__s3__tmp__new_compression__id~3 : int;
    var ssl3_connect_~s__session__cipher~3 : int;
    var ssl3_connect_~s__session__compress_meth~3 : int;
    var ssl3_connect_~buf~3 : int;
    var ssl3_connect_~tmp~3 : int;
    var ssl3_connect_~l~3 : int;
    var ssl3_connect_~num1~3 : int;
    var ssl3_connect_~cb~3 : int;
    var ssl3_connect_~ret~3 : int;
    var ssl3_connect_~new_state~3 : int;
    var ssl3_connect_~state~3 : int;
    var ssl3_connect_~skip~3 : int;
    var ssl3_connect_~tmp___0~3 : int;
    var ssl3_connect_~tmp___1~3 : int;
    var ssl3_connect_~tmp___2~3 : int;
    var ssl3_connect_~tmp___3~3 : int;
    var ssl3_connect_~tmp___4~3 : int;
    var ssl3_connect_~tmp___5~3 : int;
    var ssl3_connect_~tmp___6~3 : int;
    var ssl3_connect_~tmp___7~3 : int;
    var ssl3_connect_~tmp___8~3 : int;
    var ssl3_connect_~tmp___9~3 : int;
    var ssl3_connect_~blastFlag~3 : int;
    var ssl3_connect_~ag_X~3 : int;
    var ssl3_connect_~ag_Y~3 : int;
    var ssl3_connect_~ag_Z~3 : int;
    var ssl3_connect_~__retres60~3 : int;

  loc0:
    havoc main_#res;
    havoc main_#t~ret41, main_~__retres1~187;
    havoc main_~__retres1~187;
    havoc ssl3_connect_#res;
    havoc ssl3_connect_#t~nondet0, ssl3_connect_#t~nondet1, ssl3_connect_#t~nondet2, ssl3_connect_#t~nondet3, ssl3_connect_#t~nondet4, ssl3_connect_#t~nondet5, ssl3_connect_#t~nondet6, ssl3_connect_#t~nondet7, ssl3_connect_#t~nondet8, ssl3_connect_#t~nondet9, ssl3_connect_#t~nondet10, ssl3_connect_#t~nondet11, ssl3_connect_#t~nondet12, ssl3_connect_#t~nondet13, ssl3_connect_#t~nondet14, ssl3_connect_#t~nondet15, ssl3_connect_#t~nondet16, ssl3_connect_#t~nondet17, ssl3_connect_#t~nondet18, ssl3_connect_#t~nondet19, ssl3_connect_#t~nondet20, ssl3_connect_#t~nondet21, ssl3_connect_#t~nondet22, ssl3_connect_#t~nondet23, ssl3_connect_#t~nondet24, ssl3_connect_#t~nondet25, ssl3_connect_#t~nondet26, ssl3_connect_#t~nondet27, ssl3_connect_#t~nondet28, ssl3_connect_#t~nondet29, ssl3_connect_#t~nondet30, ssl3_connect_#t~nondet31, ssl3_connect_#t~nondet32, ssl3_connect_#t~nondet33, ssl3_connect_#t~nondet34, ssl3_connect_#t~nondet35, ssl3_connect_#t~nondet36, ssl3_connect_#t~nondet37, ssl3_connect_#t~nondet38, ssl3_connect_#t~nondet39, ssl3_connect_#t~nondet40, ssl3_connect_~s__info_callback~3, ssl3_connect_~s__in_handshake~3, ssl3_connect_~s__state~3, ssl3_connect_~s__new_session~3, ssl3_connect_~s__server~3, ssl3_connect_~s__version~3, ssl3_connect_~s__type~3, ssl3_connect_~s__init_num~3, ssl3_connect_~s__bbio~3, ssl3_connect_~s__wbio~3, ssl3_connect_~s__hit~3, ssl3_connect_~s__rwstate~3, ssl3_connect_~s__init_buf___0~3, ssl3_connect_~s__debug~3, ssl3_connect_~s__shutdown~3, ssl3_connect_~s__ctx__info_callback~3, ssl3_connect_~s__ctx__stats__sess_connect_renegotiate~3, ssl3_connect_~s__ctx__stats__sess_connect~3, ssl3_connect_~s__ctx__stats__sess_hit~3, ssl3_connect_~s__ctx__stats__sess_connect_good~3, ssl3_connect_~s__s3__change_cipher_spec~3, ssl3_connect_~s__s3__flags~3, ssl3_connect_~s__s3__delay_buf_pop_ret~3, ssl3_connect_~s__s3__tmp__cert_req~3, ssl3_connect_~s__s3__tmp__new_compression~3, ssl3_connect_~s__s3__tmp__reuse_message~3, ssl3_connect_~s__s3__tmp__new_cipher~3, ssl3_connect_~s__s3__tmp__new_cipher__algorithms~3, ssl3_connect_~s__s3__tmp__next_state___0~3, ssl3_connect_~s__s3__tmp__new_compression__id~3, ssl3_connect_~s__session__cipher~3, ssl3_connect_~s__session__compress_meth~3, ssl3_connect_~buf~3, ssl3_connect_~tmp~3, ssl3_connect_~l~3, ssl3_connect_~num1~3, ssl3_connect_~cb~3, ssl3_connect_~ret~3, ssl3_connect_~new_state~3, ssl3_connect_~state~3, ssl3_connect_~skip~3, ssl3_connect_~tmp___0~3, ssl3_connect_~tmp___1~3, ssl3_connect_~tmp___2~3, ssl3_connect_~tmp___3~3, ssl3_connect_~tmp___4~3, ssl3_connect_~tmp___5~3, ssl3_connect_~tmp___6~3, ssl3_connect_~tmp___7~3, ssl3_connect_~tmp___8~3, ssl3_connect_~tmp___9~3, ssl3_connect_~blastFlag~3, ssl3_connect_~ag_X~3, ssl3_connect_~ag_Y~3, ssl3_connect_~ag_Z~3, ssl3_connect_~__retres60~3;
    assume -2147483648 <= ssl3_connect_#t~nondet0 && ssl3_connect_#t~nondet0 <= 2147483647;
    ssl3_connect_~s__info_callback~3 := ssl3_connect_#t~nondet0;
    havoc ssl3_connect_#t~nondet0;
    assume -2147483648 <= ssl3_connect_#t~nondet1 && ssl3_connect_#t~nondet1 <= 2147483647;
    ssl3_connect_~s__in_handshake~3 := ssl3_connect_#t~nondet1;
    havoc ssl3_connect_#t~nondet1;
    havoc ssl3_connect_~s__state~3;
    havoc ssl3_connect_~s__new_session~3;
    havoc ssl3_connect_~s__server~3;
    assume -2147483648 <= ssl3_connect_#t~nondet2 && ssl3_connect_#t~nondet2 <= 2147483647;
    ssl3_connect_~s__version~3 := ssl3_connect_#t~nondet2;
    havoc ssl3_connect_#t~nondet2;
    havoc ssl3_connect_~s__type~3;
    havoc ssl3_connect_~s__init_num~3;
    assume -2147483648 <= ssl3_connect_#t~nondet3 && ssl3_connect_#t~nondet3 <= 2147483647;
    ssl3_connect_~s__bbio~3 := ssl3_connect_#t~nondet3;
    havoc ssl3_connect_#t~nondet3;
    assume -2147483648 <= ssl3_connect_#t~nondet4 && ssl3_connect_#t~nondet4 <= 2147483647;
    ssl3_connect_~s__wbio~3 := ssl3_connect_#t~nondet4;
    havoc ssl3_connect_#t~nondet4;
    assume -2147483648 <= ssl3_connect_#t~nondet5 && ssl3_connect_#t~nondet5 <= 2147483647;
    ssl3_connect_~s__hit~3 := ssl3_connect_#t~nondet5;
    havoc ssl3_connect_#t~nondet5;
    havoc ssl3_connect_~s__rwstate~3;
    havoc ssl3_connect_~s__init_buf___0~3;
    assume -2147483648 <= ssl3_connect_#t~nondet6 && ssl3_connect_#t~nondet6 <= 2147483647;
    ssl3_connect_~s__debug~3 := ssl3_connect_#t~nondet6;
    havoc ssl3_connect_#t~nondet6;
    havoc ssl3_connect_~s__shutdown~3;
    assume -2147483648 <= ssl3_connect_#t~nondet7 && ssl3_connect_#t~nondet7 <= 2147483647;
    ssl3_connect_~s__ctx__info_callback~3 := ssl3_connect_#t~nondet7;
    havoc ssl3_connect_#t~nondet7;
    assume -2147483648 <= ssl3_connect_#t~nondet8 && ssl3_connect_#t~nondet8 <= 2147483647;
    ssl3_connect_~s__ctx__stats__sess_connect_renegotiate~3 := ssl3_connect_#t~nondet8;
    havoc ssl3_connect_#t~nondet8;
    havoc ssl3_connect_~s__ctx__stats__sess_connect~3;
    assume -2147483648 <= ssl3_connect_#t~nondet9 && ssl3_connect_#t~nondet9 <= 2147483647;
    ssl3_connect_~s__ctx__stats__sess_hit~3 := ssl3_connect_#t~nondet9;
    havoc ssl3_connect_#t~nondet9;
    assume -2147483648 <= ssl3_connect_#t~nondet10 && ssl3_connect_#t~nondet10 <= 2147483647;
    ssl3_connect_~s__ctx__stats__sess_connect_good~3 := ssl3_connect_#t~nondet10;
    havoc ssl3_connect_#t~nondet10;
    havoc ssl3_connect_~s__s3__change_cipher_spec~3;
    havoc ssl3_connect_~s__s3__flags~3;
    havoc ssl3_connect_~s__s3__delay_buf_pop_ret~3;
    assume -2147483648 <= ssl3_connect_#t~nondet11 && ssl3_connect_#t~nondet11 <= 2147483647;
    ssl3_connect_~s__s3__tmp__cert_req~3 := ssl3_connect_#t~nondet11;
    havoc ssl3_connect_#t~nondet11;
    assume -2147483648 <= ssl3_connect_#t~nondet12 && ssl3_connect_#t~nondet12 <= 2147483647;
    ssl3_connect_~s__s3__tmp__new_compression~3 := ssl3_connect_#t~nondet12;
    havoc ssl3_connect_#t~nondet12;
    assume -2147483648 <= ssl3_connect_#t~nondet13 && ssl3_connect_#t~nondet13 <= 2147483647;
    ssl3_connect_~s__s3__tmp__reuse_message~3 := ssl3_connect_#t~nondet13;
    havoc ssl3_connect_#t~nondet13;
    assume -2147483648 <= ssl3_connect_#t~nondet14 && ssl3_connect_#t~nondet14 <= 2147483647;
    ssl3_connect_~s__s3__tmp__new_cipher~3 := ssl3_connect_#t~nondet14;
    havoc ssl3_connect_#t~nondet14;
    assume -2147483648 <= ssl3_connect_#t~nondet15 && ssl3_connect_#t~nondet15 <= 2147483647;
    ssl3_connect_~s__s3__tmp__new_cipher__algorithms~3 := ssl3_connect_#t~nondet15;
    havoc ssl3_connect_#t~nondet15;
    havoc ssl3_connect_~s__s3__tmp__next_state___0~3;
    assume -2147483648 <= ssl3_connect_#t~nondet16 && ssl3_connect_#t~nondet16 <= 2147483647;
    ssl3_connect_~s__s3__tmp__new_compression__id~3 := ssl3_connect_#t~nondet16;
    havoc ssl3_connect_#t~nondet16;
    havoc ssl3_connect_~s__session__cipher~3;
    havoc ssl3_connect_~s__session__compress_meth~3;
    havoc ssl3_connect_~buf~3;
    havoc ssl3_connect_~tmp~3;
    havoc ssl3_connect_~l~3;
    havoc ssl3_connect_~num1~3;
    havoc ssl3_connect_~cb~3;
    havoc ssl3_connect_~ret~3;
    havoc ssl3_connect_~new_state~3;
    havoc ssl3_connect_~state~3;
    havoc ssl3_connect_~skip~3;
    havoc ssl3_connect_~tmp___0~3;
    assume -2147483648 <= ssl3_connect_#t~nondet17 && ssl3_connect_#t~nondet17 <= 2147483647;
    ssl3_connect_~tmp___1~3 := ssl3_connect_#t~nondet17;
    havoc ssl3_connect_#t~nondet17;
    assume -2147483648 <= ssl3_connect_#t~nondet18 && ssl3_connect_#t~nondet18 <= 2147483647;
    ssl3_connect_~tmp___2~3 := ssl3_connect_#t~nondet18;
    havoc ssl3_connect_#t~nondet18;
    assume -2147483648 <= ssl3_connect_#t~nondet19 && ssl3_connect_#t~nondet19 <= 2147483647;
    ssl3_connect_~tmp___3~3 := ssl3_connect_#t~nondet19;
    havoc ssl3_connect_#t~nondet19;
    assume -2147483648 <= ssl3_connect_#t~nondet20 && ssl3_connect_#t~nondet20 <= 2147483647;
    ssl3_connect_~tmp___4~3 := ssl3_connect_#t~nondet20;
    havoc ssl3_connect_#t~nondet20;
    assume -2147483648 <= ssl3_connect_#t~nondet21 && ssl3_connect_#t~nondet21 <= 2147483647;
    ssl3_connect_~tmp___5~3 := ssl3_connect_#t~nondet21;
    havoc ssl3_connect_#t~nondet21;
    assume -2147483648 <= ssl3_connect_#t~nondet22 && ssl3_connect_#t~nondet22 <= 2147483647;
    ssl3_connect_~tmp___6~3 := ssl3_connect_#t~nondet22;
    havoc ssl3_connect_#t~nondet22;
    assume -2147483648 <= ssl3_connect_#t~nondet23 && ssl3_connect_#t~nondet23 <= 2147483647;
    ssl3_connect_~tmp___7~3 := ssl3_connect_#t~nondet23;
    havoc ssl3_connect_#t~nondet23;
    assume -2147483648 <= ssl3_connect_#t~nondet24 && ssl3_connect_#t~nondet24 <= 2147483647;
    ssl3_connect_~tmp___8~3 := ssl3_connect_#t~nondet24;
    havoc ssl3_connect_#t~nondet24;
    assume -2147483648 <= ssl3_connect_#t~nondet25 && ssl3_connect_#t~nondet25 <= 2147483647;
    ssl3_connect_~tmp___9~3 := ssl3_connect_#t~nondet25;
    havoc ssl3_connect_#t~nondet25;
    havoc ssl3_connect_~blastFlag~3;
    havoc ssl3_connect_~ag_X~3;
    havoc ssl3_connect_~ag_Y~3;
    havoc ssl3_connect_~ag_Z~3;
    havoc ssl3_connect_~__retres60~3;
    ssl3_connect_~s__state~3 := 12292;
    ssl3_connect_~blastFlag~3 := 0;
    assume -2147483648 <= ssl3_connect_#t~nondet26 && ssl3_connect_#t~nondet26 <= 2147483647;
    ssl3_connect_~tmp~3 := ssl3_connect_#t~nondet26;
    havoc ssl3_connect_#t~nondet26;
    ssl3_connect_~cb~3 := 0;
    ssl3_connect_~ret~3 := -1;
    ssl3_connect_~skip~3 := 0;
    ssl3_connect_~tmp___0~3 := 0;
    assume ssl3_connect_~s__info_callback~3 != 0;
    ssl3_connect_~cb~3 := ssl3_connect_~s__info_callback~3;
    ssl3_connect_~s__in_handshake~3 := ssl3_connect_~s__in_handshake~3 + 1;
    assume !(ssl3_connect_~tmp___1~3 + 12288 != 0);
    assume !(ssl3_connect_~s__hit~3 != 0);
    ssl3_connect_~ag_Z~3 := 48;
    goto loc1;
  loc1:
    assume true;
    assume !false;
    ssl3_connect_~state~3 := ssl3_connect_~s__state~3;
    goto loc2;
  loc2:
    goto loc2_0, loc2_1;
  loc2_0:
    assume ssl3_connect_~s__state~3 == 12292;
    ssl3_connect_~s__new_session~3 := 1;
    ssl3_connect_~s__state~3 := 4096;
    ssl3_connect_~s__ctx__stats__sess_connect_renegotiate~3 := ssl3_connect_~s__ctx__stats__sess_connect_renegotiate~3 + 1;
    ssl3_connect_~s__server~3 := 0;
    assume ssl3_connect_~cb~3 != 0;
    assume !(ssl3_connect_~s__version~3 + 65280 != 768);
    ssl3_connect_~s__type~3 := 4096;
    assume !(ssl3_connect_~s__init_buf___0~3 % 18446744073709551616 == 0);
    assume !(ssl3_connect_~tmp___4~3 == 0);
    assume !(ssl3_connect_~tmp___5~3 == 0);
    ssl3_connect_~s__state~3 := 4368;
    ssl3_connect_~s__ctx__stats__sess_connect~3 := ssl3_connect_~s__ctx__stats__sess_connect~3 + 1;
    ssl3_connect_~s__init_num~3 := 0;
    goto loc3;
  loc2_1:
    assume !(ssl3_connect_~s__state~3 == 12292);
    assume !(ssl3_connect_~s__state~3 == 16384);
    assume !(ssl3_connect_~s__state~3 == 4096);
    assume !(ssl3_connect_~s__state~3 == 20480);
    assume !(ssl3_connect_~s__state~3 == 4099);
    goto loc4;
  loc3:
    assume !(ssl3_connect_~s__s3__tmp__reuse_message~3 == 0);
    ssl3_connect_~skip~3 := 0;
    goto loc1;
  loc4:
    goto loc4_0, loc4_1;
  loc4_0:
    assume ssl3_connect_~s__state~3 == 4368;
    ssl3_connect_~s__shutdown~3 := 0;
    assume -2147483648 <= ssl3_connect_#t~nondet28 && ssl3_connect_#t~nondet28 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet28;
    havoc ssl3_connect_#t~nondet28;
    assume ssl3_connect_~blastFlag~3 == 0;
    ssl3_connect_~blastFlag~3 := 1;
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~s__state~3 := 4384;
    ssl3_connect_~ag_X~3 := ssl3_connect_~s__state~3 - 32;
    ssl3_connect_~s__init_num~3 := 0;
    assume ssl3_connect_~s__bbio~3 % 18446744073709551616 != ssl3_connect_~s__wbio~3 % 18446744073709551616;
    goto loc3;
  loc4_1:
    assume !(ssl3_connect_~s__state~3 == 4368);
    assume !(ssl3_connect_~s__state~3 == 4369);
    goto loc5;
  loc5:
    goto loc5_0, loc5_1;
  loc5_0:
    assume ssl3_connect_~s__state~3 == 4384;
    assume -2147483648 <= ssl3_connect_#t~nondet29 && ssl3_connect_#t~nondet29 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet29;
    havoc ssl3_connect_#t~nondet29;
    goto loc6;
  loc5_1:
    assume !(ssl3_connect_~s__state~3 == 4384);
    assume !(ssl3_connect_~s__state~3 == 4385);
    goto loc7;
  loc6:
    goto loc6_0, loc6_1;
  loc6_0:
    assume ssl3_connect_~blastFlag~3 == 1;
    ssl3_connect_~blastFlag~3 := 2;
    goto loc8;
  loc6_1:
    assume !(ssl3_connect_~blastFlag~3 == 1);
    assume ssl3_connect_~blastFlag~3 == 4;
    ssl3_connect_~blastFlag~3 := 5;
    goto loc8;
  loc7:
    goto loc7_0, loc7_1;
  loc7_0:
    assume ssl3_connect_~s__state~3 == 4400;
    assume !((ssl3_connect_~s__s3__tmp__new_cipher__algorithms~3 + 256) % 18446744073709551616 != 0);
    assume -2147483648 <= ssl3_connect_#t~nondet30 && ssl3_connect_#t~nondet30 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet30;
    havoc ssl3_connect_#t~nondet30;
    assume ssl3_connect_~blastFlag~3 == 2;
    ssl3_connect_~blastFlag~3 := 3;
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~s__state~3 := 4416;
    ssl3_connect_~s__init_num~3 := 0;
    goto loc3;
  loc7_1:
    assume !(ssl3_connect_~s__state~3 == 4400);
    assume !(ssl3_connect_~s__state~3 == 4401);
    goto loc9;
  loc8:
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~s__state~3 := ssl3_connect_~ag_X~3;
    assume !(ssl3_connect_~s__hit~3 != 0);
    ssl3_connect_~s__state~3 := ~bitwiseOr(ssl3_connect_~s__state~3, ssl3_connect_~ag_Z~3);
    ssl3_connect_~s__init_num~3 := 0;
    goto loc3;
  loc9:
    goto loc9_0, loc9_1;
  loc9_0:
    assume ssl3_connect_~s__state~3 == 4416;
    assume -2147483648 <= ssl3_connect_#t~nondet31 && ssl3_connect_#t~nondet31 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet31;
    havoc ssl3_connect_#t~nondet31;
    assume ssl3_connect_~blastFlag~3 == 3;
    ssl3_connect_~blastFlag~3 := 4;
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~s__state~3 := 4432;
    ssl3_connect_~s__init_num~3 := 0;
    assume !(ssl3_connect_~tmp___6~3 == 0);
    goto loc3;
  loc9_1:
    assume !(ssl3_connect_~s__state~3 == 4416);
    assume !(ssl3_connect_~s__state~3 == 4417);
    goto loc10;
  loc10:
    goto loc10_0, loc10_1;
  loc10_0:
    assume ssl3_connect_~s__state~3 == 4432;
    assume -2147483648 <= ssl3_connect_#t~nondet32 && ssl3_connect_#t~nondet32 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet32;
    havoc ssl3_connect_#t~nondet32;
    goto loc11;
  loc10_1:
    assume !(ssl3_connect_~s__state~3 == 4432);
    assume !(ssl3_connect_~s__state~3 == 4433);
    goto loc12;
  loc11:
    goto loc11_0, loc11_1;
  loc11_0:
    assume ssl3_connect_~blastFlag~3 == 5;
    assume !false;
    goto loc13;
  loc11_1:
    assume !(ssl3_connect_~blastFlag~3 == 5);
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~s__state~3 := 4448;
    ssl3_connect_~s__init_num~3 := 0;
    goto loc3;
  loc12:
    goto loc12_0, loc12_1;
  loc12_0:
    assume ssl3_connect_~s__state~3 == 4448;
    assume -2147483648 <= ssl3_connect_#t~nondet33 && ssl3_connect_#t~nondet33 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet33;
    havoc ssl3_connect_#t~nondet33;
    assume !(ssl3_connect_~ret~3 <= 0);
    assume !(ssl3_connect_~s__s3__tmp__cert_req~3 != 0);
    ssl3_connect_~s__state~3 := 4480;
    ssl3_connect_~s__init_num~3 := 0;
    goto loc3;
  loc12_1:
    assume !(ssl3_connect_~s__state~3 == 4448);
    assume !(ssl3_connect_~s__state~3 == 4449);
    assume !(ssl3_connect_~s__state~3 == 4464);
    assume !(ssl3_connect_~s__state~3 == 4465);
    assume !(ssl3_connect_~s__state~3 == 4466);
    assume !(ssl3_connect_~s__state~3 == 4467);
    goto loc14;
  loc13:
    assert false;
  loc14:
    goto loc14_0, loc14_1;
  loc14_0:
    assume ssl3_connect_~s__state~3 == 4480;
    assume -2147483648 <= ssl3_connect_#t~nondet35 && ssl3_connect_#t~nondet35 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet35;
    havoc ssl3_connect_#t~nondet35;
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~l~3 := ssl3_connect_~s__s3__tmp__new_cipher__algorithms~3;
    assume !(ssl3_connect_~s__s3__tmp__cert_req~3 == 1);
    ssl3_connect_~s__state~3 := 4512;
    ssl3_connect_~s__s3__change_cipher_spec~3 := 0;
    ssl3_connect_~s__init_num~3 := 0;
    goto loc3;
  loc14_1:
    assume !(ssl3_connect_~s__state~3 == 4480);
    assume !(ssl3_connect_~s__state~3 == 4481);
    assume !(ssl3_connect_~s__state~3 == 4496);
    assume !(ssl3_connect_~s__state~3 == 4497);
    goto loc15;
  loc15:
    goto loc15_0, loc15_1;
  loc15_0:
    assume ssl3_connect_~s__state~3 == 4512;
    assume -2147483648 <= ssl3_connect_#t~nondet37 && ssl3_connect_#t~nondet37 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet37;
    havoc ssl3_connect_#t~nondet37;
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~s__state~3 := 4528;
    ssl3_connect_~s__init_num~3 := 0;
    ssl3_connect_~s__session__cipher~3 := ssl3_connect_~s__s3__tmp__new_cipher~3;
    assume ssl3_connect_~s__s3__tmp__new_compression~3 == 0;
    ssl3_connect_~s__session__compress_meth~3 := 0;
    assume !(ssl3_connect_~tmp___7~3 == 0);
    assume !(ssl3_connect_~tmp___8~3 == 0);
    goto loc3;
  loc15_1:
    assume !(ssl3_connect_~s__state~3 == 4512);
    assume !(ssl3_connect_~s__state~3 == 4513);
    goto loc16;
  loc16:
    goto loc16_0, loc16_1;
  loc16_0:
    assume ssl3_connect_~s__state~3 == 4528;
    assume -2147483648 <= ssl3_connect_#t~nondet38 && ssl3_connect_#t~nondet38 <= 2147483647;
    ssl3_connect_~ret~3 := ssl3_connect_#t~nondet38;
    havoc ssl3_connect_#t~nondet38;
    assume !(ssl3_connect_~ret~3 <= 0);
    ssl3_connect_~s__state~3 := 4352;
    ssl3_connect_~s__s3__flags~3 := (if (ssl3_connect_~s__s3__flags~3 + -5) % 4294967296 <= 2147483647 then (ssl3_connect_~s__s3__flags~3 + -5) % 4294967296 else (ssl3_connect_~s__s3__flags~3 + -5) % 4294967296 - 4294967296);
    assume !(ssl3_connect_~s__hit~3 != 0);
    ssl3_connect_~s__s3__tmp__next_state___0~3 := 4560;
    ssl3_connect_~s__init_num~3 := 0;
    goto loc3;
  loc16_1:
    assume !(ssl3_connect_~s__state~3 == 4528);
    assume !(ssl3_connect_~s__state~3 == 4529);
    assume !(ssl3_connect_~s__state~3 == 4560);
    assume !(ssl3_connect_~s__state~3 == 4561);
    assume ssl3_connect_~s__state~3 == 4352;
    assume !(ssl3_connect_~num1~3 > 0);
    ssl3_connect_~s__state~3 := ssl3_connect_~s__s3__tmp__next_state___0~3;
    goto loc3;
}

procedure ULTIMATE.start() returns ();
modifies ;
modifies ;

