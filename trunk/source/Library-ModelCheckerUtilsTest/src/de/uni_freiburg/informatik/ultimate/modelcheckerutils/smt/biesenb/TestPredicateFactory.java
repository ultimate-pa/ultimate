/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class TestPredicateFactory {

	private ManagedScript mMgdScript;
	private Script mScript;
	
	public TestPredicateFactory(final ManagedScript mgdScript) {
		mMgdScript = mgdScript;
		mScript = mMgdScript.getScript();
	}
	
	public TestPredicate pred(final String op, final IProgramVar var, final int value) {
		return new TestPredicate(mScript.term(op, var.getTermVariable(), mScript.numeral(String.valueOf(value))),
				Collections.singleton(var), mScript);
	}

	public TestPredicate neg(final TestPredicate pred) {
		return new TestPredicate(mScript.term("not", pred.getFormula()), pred.getVars(), mScript);
	}

	public TestPredicate and(final TestPredicate... preds) {
		if (preds == null || preds.length < 2) {
			throw new IllegalArgumentException();
		}
		final List<Term> operands = Arrays.stream(preds).map(a -> a.getFormula()).collect(Collectors.toList());
		final Set<IProgramVar> vars = Arrays.stream(preds).map(a -> a.getVars()).reduce(new HashSet<>(),
				(a, b) -> DataStructureUtils.union(a, b));
		return new TestPredicate(SmtUtils.and(mScript, operands), vars, mScript);
	}
	
	public TestPredicate or(final TestPredicate... preds) {
		if (preds == null || preds.length < 2) {
			throw new IllegalArgumentException();
		}
		final List<Term> operands = Arrays.stream(preds).map(a -> a.getFormula()).collect(Collectors.toList());
		final Set<IProgramVar> vars = Arrays.stream(preds).map(a -> a.getVars()).reduce(new HashSet<>(),
				(a, b) -> DataStructureUtils.union(a, b));
		return new TestPredicate(SmtUtils.or(mScript, operands), vars, mScript);
	}

	public IProgramNonOldVar constructProgramVar(final String identifier) {
		BoogieOldVar oldVar;
		final Object lock = new Object();
		final Sort sort = SmtSortUtils.getIntSort(mScript);
		{
			final boolean isOldVar = true;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, null, true, isOldVar);
			final TermVariable termVariable = mScript.variable(name, sort);
			mMgdScript.lock(lock);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mMgdScript, lock, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mMgdScript, lock, sort, name);
			mMgdScript.unlock(lock);
			oldVar = new BoogieOldVar(identifier, null, termVariable, defaultConstant, primedConstant);
		}
		BoogieNonOldVar nonOldVar;
		{
			final boolean isOldVar = false;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, null, true, isOldVar);
			final TermVariable termVariable = mScript.variable(name, sort);
			mMgdScript.lock(lock);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mMgdScript, lock, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mMgdScript, lock, sort, name);
			mMgdScript.unlock(lock);
			nonOldVar = new BoogieNonOldVar(identifier, null, termVariable, defaultConstant, primedConstant, oldVar);
		}
		oldVar.setNonOldVar(nonOldVar);
		return nonOldVar;
	}
}
