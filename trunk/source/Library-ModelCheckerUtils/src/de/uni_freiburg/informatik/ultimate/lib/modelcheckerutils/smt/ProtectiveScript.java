package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

public class ProtectiveScript extends WrapperScript{
	private static final String EXCEPTIONTXT = "unallowed operation";

	public ProtectiveScript(final Script script) {
		super(script);
	}
	
	@Override
	public void push(final int levels) throws SMTLIBException {
		throw new AssertionError(EXCEPTIONTXT);
	}
	
	@Override
	public void pop(final int levels) throws SMTLIBException {
		throw new AssertionError(EXCEPTIONTXT);
	}
	
	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		throw new AssertionError(EXCEPTIONTXT);
	}
	
	@Override
	public void resetAssertions() {
		throw new AssertionError(EXCEPTIONTXT);
	}
	
	@Override
	public void reset() {
		throw new AssertionError(EXCEPTIONTXT);
	}

}
