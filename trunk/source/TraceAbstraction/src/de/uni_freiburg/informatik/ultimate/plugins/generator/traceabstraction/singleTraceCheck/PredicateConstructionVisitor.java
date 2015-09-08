/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
