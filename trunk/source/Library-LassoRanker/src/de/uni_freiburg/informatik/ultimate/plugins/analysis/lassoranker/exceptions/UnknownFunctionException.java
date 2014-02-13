package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;


/**
 * This exception is thrown if an application term containing an unknown
 * function symbol was encountered.
 * 
 * @author Jan Leike
 */
public class UnknownFunctionException extends TermException {
	
	private static final long serialVersionUID = 105590526570839700L;
	
	public UnknownFunctionException(ApplicationTerm term) {
		super("Unknown function symbol: " + term.getFunction().getName(), term);
	}
}
