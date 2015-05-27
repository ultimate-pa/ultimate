package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;

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
	
	/**
	 * Given a term in which every free variable is the TermVariable of a 
	 * BoogieVar. Compute the BoogieVars of the free variables and the 
	 * procedures of these BoogieVariables.
	 * If replaceNonModifiableOldVars is true, modifiableGlobals must be non-null
	 * and we check we replace the oldVars of all non-modifiable Globals by
	 * their corresponding non-oldVars.
	 * 
	 * 2015-05-27 Matthias: At the moment, I don't know if we need this method.
	 * Don't use it unless you know what you do.
	 */
	@Deprecated
	private static TermVarsProc computeTermVarsProc(Term term, Boogie2SMT boogie2smt, 
			boolean replaceNonModifiableOldVars, Set<BoogieVar> modifiableGlobals) {
		HashSet<BoogieVar> vars = new HashSet<BoogieVar>();
		List<BoogieOldVar> oldVarsThatHaveToBeReplaced = new ArrayList<>();
		Set<String> procs = new HashSet<String>();
		for (TermVariable tv : term.getFreeVars()) {
			BoogieVar bv = boogie2smt.getBoogie2SmtSymbolTable().getBoogieVar(tv);
			if (bv == null) {
				throw new AssertionError("No corresponding BoogieVar for " + tv);
			}
			if (replaceNonModifiableOldVars) {
				if (bv instanceof BoogieOldVar) {
					BoogieNonOldVar nonOld = ((BoogieOldVar) bv).getNonOldVar();
					if (modifiableGlobals.contains(nonOld)) {
						// do nothing - is modifiable
					} else {
						oldVarsThatHaveToBeReplaced.add((BoogieOldVar) bv);
						bv = nonOld;
					}
				}
			}
			vars.add(bv);
			if (bv.getProcedure() != null) {
				procs.add(bv.getProcedure());
			}
		}
		if (!oldVarsThatHaveToBeReplaced.isEmpty()) {
			Map<Term, Term> substitutionMapping = new HashMap<>();
			for (BoogieOldVar oldVar : oldVarsThatHaveToBeReplaced) {
				BoogieNonOldVar nonOld = ((BoogieOldVar) oldVar).getNonOldVar();
				substitutionMapping.put(oldVar.getTermVariable(), nonOld.getTermVariable());
			}
			term = (new SafeSubstitution(boogie2smt.getScript(), substitutionMapping)).transform(term);
		}
		Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, boogie2smt.getScript());
		return new TermVarsProc(term, vars, procs.toArray(new String[procs.size()]), closedTerm);
	}


}