/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class TermVarsFuns {
	private final Term mTerm;
	private final Set<IProgramVar> mVars;
	private final Set<IProgramFunction> mFuns;
	private final Term mClosedTerm;

	public TermVarsFuns(final Term term, final Set<IProgramVar> vars, final Set<IProgramFunction> funs,
			final Term closedTerm) {
		mTerm = term;
		mVars = vars;
		mFuns = funs;
		mClosedTerm = closedTerm;
	}

	public Term getFormula() {
		return mTerm;
	}

	public Term getClosedFormula() {
		return mClosedTerm;
	}

	public Set<IProgramVar> getVars() {
		return mVars;
	}

	public Set<IProgramFunction> getFuns() {
		return mFuns;
	}

	/**
	 * Given a term in which every free variable is the TermVariable of an {@link IProgramVar}, compute the
	 * {@link IProgramVar}s of the free variables, and the {@link IProgramFunction}s appearing in the term.
	 */
	public static TermVarsFuns computeTermVarsFuns(final Term term, final ManagedScript mgdScript,
			final IIcfgSymbolTable symbolTable) {
		return computeTermVarsProc(term, mgdScript, symbolTable::getProgramVar, symbolTable::getProgramFun);
	}

	/**
	 * Given a term in which every free variable is the TermVariable of an {@link IProgramVar}, compute the
	 * {@link IProgramVar}s of the free variables, and the {@link IProgramFunction}s appearing in the term.
	 */
	public static TermVarsFuns computeTermVarsProc(final Term term, final ManagedScript mgdScript,
			final Function<TermVariable, IProgramVar> funTermVar2ProgVar,
			final Function<FunctionSymbol, IProgramFunction> funcSymb2ProgFunc) {
		final HashSet<IProgramVar> vars = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar bv = funTermVar2ProgVar.apply(tv);
			if (bv == null) {
				throw new AssertionError("No corresponding IProgramVar for " + tv);
			}
			vars.add(bv);
		}
		final Set<ApplicationTerm> nonTheoryAppTerms = findNonTheoryApplicationTerms(term);
		Set<IProgramFunction> programFunctions;
		if (nonTheoryAppTerms.isEmpty()) {
			programFunctions = Collections.emptySet();
		} else {
			final Set<IProgramFunction> tmp = new HashSet<>();
			for (final ApplicationTerm nonTheoryAppTerm : nonTheoryAppTerms) {
				final IProgramFunction progFunc = funcSymb2ProgFunc.apply(nonTheoryAppTerm.getFunction());
				if (progFunc == null) {
					throw new AssertionError("No corresponding IProgramFunction for " + nonTheoryAppTerm.getFunction());
				}
				tmp.add(progFunc);
			}
			programFunctions = DataStructureUtils.getUnmodifiable(tmp);
		}

		final Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, mgdScript);
		return new TermVarsFuns(term, vars, programFunctions, closedTerm);
	}

	public static Set<ApplicationTerm> findNonTheoryApplicationTerms(final Term term) {
		final Predicate<Term> isNonTheoryApplicationTerm =
				(x -> ((x instanceof ApplicationTerm) && !((ApplicationTerm) x).getFunction().isIntern()));
		final Set tmp = SubTermFinder.find(term, isNonTheoryApplicationTerm, false);
		final Set<ApplicationTerm> nonTheoryAppTerms = tmp;
		return nonTheoryAppTerms;
	}
}
