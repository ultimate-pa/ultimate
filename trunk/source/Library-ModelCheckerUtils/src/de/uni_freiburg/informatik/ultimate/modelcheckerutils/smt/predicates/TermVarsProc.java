package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;

public class TermVarsProc {
	private final Term m_Term;
	private final Set<BoogieVar> m_Vars;
	private final String[] m_Procedures;
	private final Term m_ClosedTerm;
	
	public TermVarsProc(Term term, Set<BoogieVar> vars,
			String[] procedures, Term closedTerm) {
		m_Term = term;
		m_Vars = vars;
		m_Procedures = procedures;
		m_ClosedTerm = closedTerm;
	}

	public String[] getProcedures() {
		return m_Procedures;
	}

	public Term getFormula() {
		return m_Term;
	}

	public Term getClosedFormula() {
		return m_ClosedTerm;
	}

	public Set<BoogieVar> getVars() {
		return m_Vars;
	}
	
	
	
	/**
	 * Given a term in which every free variable is the TermVariable of a 
	 * BoogieVar. Compute the BoogieVars of the free variables and the 
	 * procedures of these BoogieVariables.
	 */
	public static TermVarsProc computeTermVarsProc(Term term, Boogie2SMT boogie2smt) {
		HashSet<BoogieVar> vars = new HashSet<BoogieVar>();
		Set<String> procs = new HashSet<String>();
		for (TermVariable tv : term.getFreeVars()) {
			BoogieVar bv = boogie2smt.getBoogie2SmtSymbolTable().getBoogieVar(tv);
			if (bv == null) {
				throw new AssertionError("No corresponding BoogieVar for " + tv);
			}
			vars.add(bv);
			if (bv.getProcedure() != null) {
				procs.add(bv.getProcedure());
			}
		}
		Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, boogie2smt.getScript());
		return new TermVarsProc(term, vars, procs.toArray(new String[procs.size()]), closedTerm);
	}

}