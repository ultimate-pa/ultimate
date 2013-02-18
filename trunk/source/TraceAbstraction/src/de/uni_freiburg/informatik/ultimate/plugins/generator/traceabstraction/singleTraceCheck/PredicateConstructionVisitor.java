package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaWalker.SymbolVisitor;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

/**
 * Traverse a Term top-down and replace all subterms which occur as key of
 * the Map term2BoogieVars by the value of term2BoogieVars.
 * Furthermore all replaced BoogieVars are stored in m_Vars and if the BoogieVar
 * has a procedure, the procedure is stored in m_Procedure.
 * 
 * This may only applied to formulas such that the result contains only global
 * BoogieVars and BoogieVars of a single procedure.
 * 
 * This class is used to construct Predicates from, given craig interpolants
 * obtained from checking satisfiability of an SSA. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class PredicateConstructionVisitor implements SymbolVisitor {

	Map<Term, BoogieVar> m_term2BoogieVars;
	
	Set<BoogieVar> m_Vars;
	Set<String> m_Procedures;
	
	
	public PredicateConstructionVisitor(Map<Term, BoogieVar> term2BoogieVars)
	{
		m_term2BoogieVars = term2BoogieVars;
		m_Vars = null;
		m_Procedures = new HashSet<String>();
	}

	public void clearVarsAndProc() {
		m_Vars = new HashSet<BoogieVar>();
		m_Procedures = new HashSet<String>();
	}
	
	public Set<BoogieVar> getVars() {
		return m_Vars;
	}
	
	public Set<String> getProcedure() {
		return m_Procedures;
	}
	
	
	   
	
	@Override
	public void quantifier(TermVariable[] tvs) {}

	@Override
	public Term term (Term input) {
		if (m_term2BoogieVars.containsKey(input)) {
			BoogieVar bv = m_term2BoogieVars.get(input);
			assert bv != null;
			if (bv.getProcedure() != null) {
				m_Procedures.add(bv.getProcedure());
			}
			m_Vars.add(bv);
			Term termVariable = bv.getTermVariable();
			return termVariable;
		}
		else if (input instanceof ConstantTerm) {
			return input;
		}
		else {
			return null;
		}
	}

	@Override
	public boolean unflet() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean unlet() {
		throw new UnsupportedOperationException();
	}

	@Override
	public void let(TermVariable[] tv, Term[] mval) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void endscope(TermVariable[] tv) {
		// TODO Auto-generated method stub		
	}

	@Override
	public void done(Term input) {
		// TODO Auto-generated method stub
		
	}
	
}
