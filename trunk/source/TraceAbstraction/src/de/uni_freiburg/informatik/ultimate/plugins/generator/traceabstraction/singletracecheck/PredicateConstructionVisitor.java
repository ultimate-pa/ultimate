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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaWalker.SymbolVisitor;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Traverse a Term top-down and replace all subterms which occur as key of the Map term2BoogieVars by the value of
 * term2BoogieVars. Furthermore all replaced BoogieVars are stored in mVars and if the BoogieVar has a procedure, the
 * procedure is stored in mProcedure.
 *
 * This may only applied to formulas such that the result contains only global BoogieVars and BoogieVars of a single
 * procedure.
 *
 * This class is used to construct Predicates from, given craig interpolants obtained from checking satisfiability of an
 * SSA.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class PredicateConstructionVisitor implements SymbolVisitor {

	Map<Term, IProgramVar> mterm2BoogieVars;

	Set<IProgramVar> mVars;
	Set<String> mProcedures;

	public PredicateConstructionVisitor(final Map<Term, IProgramVar> term2BoogieVars) {
		mterm2BoogieVars = term2BoogieVars;
		mVars = null;
		mProcedures = new HashSet<>();
	}

	public void clearVarsAndProc() {
		mVars = new HashSet<>();
		mProcedures = new HashSet<>();
	}

	public Set<IProgramVar> getVars() {
		return mVars;
	}

	public Set<String> getProcedure() {
		return mProcedures;
	}

	@Override
	public void quantifier(final TermVariable[] tvs) {
	}

	@Override
	public Term term(final Term input) {
		if (mterm2BoogieVars.containsKey(input)) {
			final IProgramVar bv = mterm2BoogieVars.get(input);
			assert bv != null;
			if (bv.getProcedure() != null) {
				mProcedures.add(bv.getProcedure());
			}
			mVars.add(bv);
			final Term termVariable = bv.getTermVariable();
			return termVariable;
		} else if (input instanceof ConstantTerm) {
			return input;
		} else {
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
	public void let(final TermVariable[] tv, final Term[] mval) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void endscope(final TermVariable[] tv) {
		// TODO Auto-generated method stub
	}

	@Override
	public void done(final Term input) {
		// TODO Auto-generated method stub

	}

}
