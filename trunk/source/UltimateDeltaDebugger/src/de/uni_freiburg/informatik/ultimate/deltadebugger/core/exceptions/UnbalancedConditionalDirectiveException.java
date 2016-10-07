package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

public class UnbalancedConditionalDirectiveException extends ParserException {

    public UnbalancedConditionalDirectiveException(){
        super();
    }

    public UnbalancedConditionalDirectiveException(String message){
        super(message);
    }
	
}
