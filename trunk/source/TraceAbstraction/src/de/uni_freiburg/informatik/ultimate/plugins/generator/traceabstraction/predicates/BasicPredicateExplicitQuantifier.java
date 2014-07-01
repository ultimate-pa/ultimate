package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;

public class BasicPredicateExplicitQuantifier extends BasicPredicate {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -2401826317961930222L;
	private final int m_Quantifier;
	private final Set<TermVariable> m_QuantifiedVariables;

	protected BasicPredicateExplicitQuantifier(int serialNumber,
			String[] procedures, Term term, Set<BoogieVar> vars,
			Term closedFormula, int quantifier, Set<TermVariable> quantifiedVariables) {
		super(serialNumber, procedures, term, vars, closedFormula);
		assert quantifier == QuantifiedFormula.EXISTS || quantifier == QuantifiedFormula.FORALL;
		m_Quantifier = quantifier;
		m_QuantifiedVariables = quantifiedVariables;
	}

	public int getQuantifier() {
		return m_Quantifier;
	}

	public Set<TermVariable> getQuantifiedVariables() {
		return m_QuantifiedVariables;
	}
	
}
