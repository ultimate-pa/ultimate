package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class DebugPredicate implements IPredicate {
	
	private final String m_DebugMessage;
	private final int m_SerialNumber;
	private final Term m_Term;
	
	public DebugPredicate(String debugMessage, int serialNumber, Term dontCareTerm) {
		m_DebugMessage = debugMessage;
		m_SerialNumber = serialNumber;
		m_Term = dontCareTerm;
	}

	@Override
	public String[] getProcedures() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term getFormula() {
		return m_Term;
	}

	@Override
	public Term getClosedFormula() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<BoogieVar> getVars() {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public String toString() {
		return m_DebugMessage;
	}
	
	@Override
	public int hashCode() {
		return m_SerialNumber;
	}

}
