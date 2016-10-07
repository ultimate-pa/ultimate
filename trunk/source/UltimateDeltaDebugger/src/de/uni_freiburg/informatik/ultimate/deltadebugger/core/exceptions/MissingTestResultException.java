package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

public class MissingTestResultException extends RuntimeException {

    public MissingTestResultException(){
        super();
    }

    public MissingTestResultException(String message){
        super(message);
    }
	
}
