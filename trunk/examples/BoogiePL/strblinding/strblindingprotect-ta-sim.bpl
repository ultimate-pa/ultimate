type message;
const unique MSG_NOT_BLINDED, MSG_POTENTIALLY_BLINDED, MSG_BLINDED,
    MSG_INSIDE_APOGEE, MSG_OUTSIDE_APOGEE : message;

type States;
const unique NOTBLINDED, POTENTIALLYBLIND, BLINDED, INAPOGEE : States;

const CS_ONLY : int;
axiom CS_ONLY == 7;

var ctxt.TA : int;
var ctxt.state : States;
var ctxt.num_of_str_blinded : int;
var ctxt.num_of_str_pred_blinded : int;

procedure out_msg(_msg: message);
procedure function_active(_active : bool);

procedure get_true_anomaly(_ta: int)
    modifies ctxt.TA, ctxt.state;
{
    if  (ctxt.state == NOTBLINDED) {
        ctxt.TA := _ta;
        call runTransition(1);
    } else if (ctxt.state == POTENTIALLYBLIND) {
        ctxt.TA := _ta;
        call runTransition(4);
    } else if (ctxt.state == BLINDED) {
        call runTransition(CS_ONLY);
    } else if (ctxt.state == INAPOGEE) {
        ctxt.TA := _ta;
        call runTransition(6);
    } else {
        call runTransition(CS_ONLY);
    }
}

procedure STR_blinded(_num_str_blind: int)
    modifies ctxt.num_of_str_blinded, ctxt.state;
{
    if  (ctxt.state == NOTBLINDED) {
        call runTransition(CS_ONLY);
    } else if (ctxt.state == POTENTIALLYBLIND) {
        ctxt.num_of_str_blinded := _num_str_blind;
        call runTransition(3);
    } else if (ctxt.state == BLINDED) {
        call runTransition(CS_ONLY);
    } else if (ctxt.state == INAPOGEE) {
        ctxt.num_of_str_blinded := _num_str_blind;
        call runTransition(5);
    } else {
        call runTransition(CS_ONLY);
    }
}

procedure pred_blinded(_num_pred_blind: int)
    modifies ctxt.num_of_str_pred_blinded, ctxt.state;
{
    if  (ctxt.state == NOTBLINDED) {
        call runTransition(CS_ONLY);
    } else if (ctxt.state == POTENTIALLYBLIND) {
        ctxt.num_of_str_pred_blinded := _num_pred_blind;
        call runTransition(2);
    } else if (ctxt.state == BLINDED) {
        call runTransition(CS_ONLY);
    } else if (ctxt.state == INAPOGEE) {
        call runTransition(CS_ONLY);
    } else {
        call runTransition(CS_ONLY);
    }
}
      

procedure runTransition(id: int)
    modifies ctxt.state;
{
    var trId : int;

    trId := id;
    while (trId != -1) {
        if (trId == 0) {
            call out_msg(MSG_NOT_BLINDED);
            call function_active(false);
            trId := -1;
            ctxt.state := NOTBLINDED;
        } else if (trId == 1) {
            if (ctxt.TA > 100) {
                call out_msg(MSG_INSIDE_APOGEE);
                trId := -1;
                ctxt.state := INAPOGEE;
            } else {
                trId := -1;
                ctxt.state := NOTBLINDED;
            }
        } else if (trId == 2) {
            if (ctxt.num_of_str_pred_blinded == 3) {
                call out_msg(MSG_BLINDED);
                call function_active(true);
                trId := -1;
                ctxt.state := BLINDED;
            } else {
                trId := -1;
                ctxt.state := POTENTIALLYBLIND;
            }
        } else if (trId == 3) {
            if (ctxt.num_of_str_blinded == 3) {
                trId := -1;
                ctxt.state := POTENTIALLYBLIND;
            } else {
                call out_msg(MSG_NOT_BLINDED);
                trId := -1;
                ctxt.state := INAPOGEE;
            }
        } else if (trId == 4) {
            if (ctxt.TA > 260) {
                call out_msg(MSG_OUTSIDE_APOGEE);
                trId := -1;
                ctxt.state := NOTBLINDED;
            } else {
                trId := -1;
                ctxt.state := POTENTIALLYBLIND;
            }
        } else if (trId == 5) {
            if (ctxt.num_of_str_blinded == 3) {
                call out_msg(MSG_POTENTIALLY_BLINDED);
                trId := -1;
                ctxt.state := POTENTIALLYBLIND;
            } else {
                trId := -1;
                ctxt.state := INAPOGEE;
            }
        } else if (trId == 6) {
            if (ctxt.TA > 260) {
                call out_msg(MSG_OUTSIDE_APOGEE);
                trId := -1;
                ctxt.state := NOTBLINDED;
            } else {
                trId := -1;
                ctxt.state := INAPOGEE;
            }
        } else if (trId == CS_ONLY) {
            trId := -1;
        }
        assert((ctxt.state == INAPOGEE) ==> (100 <= ctxt.TA && ctxt.TA <= 260));
    } 
}


procedure ULTIMATE.start()
    modifies ctxt.state, ctxt.TA, ctxt.num_of_str_blinded, ctxt.num_of_str_pred_blinded;
{
    var _ta : int;
    var _arg : int;
    
    call runTransition(0);
    _ta := 0;
    while (*) {
        if (*) {
            havoc _arg;
            assume _ta <= _arg && _arg <= _ta + 90;
            if (_arg >= 360) {
               _arg := _arg - 360;
            } 
            call get_true_anomaly(_arg);
            _ta := _arg;
        } else if (*) {
            havoc _arg;
            call STR_blinded(_arg);
        } else if (*) {
            havoc _arg;
            call pred_blinded(_arg);
        }
    }
}
