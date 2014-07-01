package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class BuchiPredicate extends BasicPredicate {
	
	private static final long serialVersionUID = 8005823999426746457L;
	private final Set<IPredicate> m_Conjuncts;

	protected BuchiPredicate(int serialNumber, String[] procedures, Term term,
			Set<BoogieVar> vars, Term closedFormula, Set<IPredicate> conjuncts) {
		super(serialNumber, procedures, term, vars, closedFormula);
		m_Conjuncts = conjuncts;

	}

	public Set<IPredicate> getConjuncts() {
		return m_Conjuncts;
	}
	
	

}
