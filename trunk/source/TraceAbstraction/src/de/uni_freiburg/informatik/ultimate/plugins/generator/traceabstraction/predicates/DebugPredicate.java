package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

public class DebugPredicate implements IPredicate {
	
	private final String m_DebugMessage;
	private final int m_SerialNumber;
	
	public DebugPredicate(String debugMessage, int serialNumber) {
		m_DebugMessage = debugMessage;
		m_SerialNumber = serialNumber;
	}

	@Override
	public String[] getProcedures() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term getFormula() {
		return SmtManager.getDontCareTerm();
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
