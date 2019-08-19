/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Computes supporting invariants that have the form of equalities and not equal relations (negated equalities). A
 * supporting invariant of a lasso program is a formula φ over program variables such that the following two
 * implications hold.
 * <ul>
 * <li>post(true, stem) ==> φ</li>
 * <li>post(φ, loop) ==> φ</li>
 * </ul>
 *
 * The name supporting invariant which is commonly used in the literature refers to the fact that these invariants are
 * used to support the synthesis of ranking functions.
 *
 * The analysis implemented in this class expects a set of {@link Doubleton}s over terms (unordered pairs of terms) and
 * checks for each pair (t1,t2) if the equality t1=t2 or the not-equals relation t1!=t2 is an invariant at the program
 * point between stem and loop.
 *
 * Note that the free variables that occur in the terms must be the default TermVariables of {@link IProgramVar}s. This
 * means that you cannot directly (without an additional substitution) use terms of {@link TransFormulas} (where we have
 * primed and unprimed versions of these TermVariables).
 *
 * We currently use this analysis to infer equality information about array indices. Our Doubletons entries from pairs
 * of array indices. We use the equality (resp. not equals) information to detect which array cells are
 * similar/different. E.g., a[x,y] and a[v,w] refer to the same array cell if x==y and y==w holds, and both expressions
 * refer to a different array cell if x!=y or y!=w holds.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class EqualitySupportingInvariantAnalysis {
	private final Set<Doubleton<Term>> mAllDoubletons;
	private final Script mScript;
	private final IIcfgSymbolTable mSymbolTable;

	private final Set<Doubleton<Term>> mDistinctDoubletons = new HashSet<>();
	private final Set<Doubleton<Term>> mEqualDoubletons = new HashSet<>();
	private final Set<Doubleton<Term>> mUnknownDoubletons = new HashSet<>();

	private final UnmodifiableTransFormula mOriginalStem;
	private final UnmodifiableTransFormula mOriginalLoop;
	private final Set<IProgramNonOldVar> mModifiableGlobalsAtStart;
	private final Set<IProgramNonOldVar> mModifiableGlobalsAtHonda;

	/**
	 *
	 * @param doubletons
	 *            set of all Doubletons that should be analyzed
	 * @param symbolTable
	 *            symbol table of the cfg
	 * @param originalStem
	 *            stem of lasso program. This must be the original, unprocessed TransFormula.
	 * @param originalLoop
	 *            loop of lasso program. This must be the original, unprocessed TransFormula.
	 * @param modifiableGlobalsAtHonda
	 *            set of all global program variables that are modifiable at the program point between stem and loop.
	 */
	public EqualitySupportingInvariantAnalysis(final Set<Doubleton<Term>> doubletons,
			final IIcfgSymbolTable symbolTable, final Script script, final UnmodifiableTransFormula originalStem,
			final UnmodifiableTransFormula originalLoop, final Set<IProgramNonOldVar> modifiableGlobalsAtHonda) {
		super();
		mSymbolTable = symbolTable;
		mScript = script;
		mOriginalStem = originalStem;
		mOriginalLoop = originalLoop;
		mModifiableGlobalsAtStart = Collections.emptySet();
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		mAllDoubletons = doubletons;

		mScript.echo(new QuotedObject("starting equality analysis for array indices of a lasso"));
		for (final Doubleton<Term> doubleton : mAllDoubletons) {
			final boolean equalityIsInvariant = isInVariant(doubleton, true);
			if (equalityIsInvariant) {
				addEqualDoubleton(doubleton);
			} else {
				final boolean notEqualIsInvariant = isInVariant(doubleton, false);
				if (notEqualIsInvariant) {
					addDistinctDoubleton(doubleton);
				} else {
					addUnknownDoubleton(doubleton);
				}
			}
		}
		mScript.echo(new QuotedObject("finished equality analysis for array indices of a lasso"));
	}

	private void addDistinctDoubleton(final Doubleton<Term> doubleton) {
		mDistinctDoubletons.add(doubleton);
	}

	private void addEqualDoubleton(final Doubleton<Term> doubleton) {
		mEqualDoubletons.add(doubleton);
	}

	private void addUnknownDoubleton(final Doubleton<Term> doubleton) {
		mUnknownDoubletons.add(doubleton);
	}

	private boolean isInVariant(final Doubleton<Term> definingDoubleton, final boolean checkEquals) {
		final Term invariantCandidateTerm;
		if (checkEquals) {
			invariantCandidateTerm = EqualityAnalysisResult.equalTerm(mScript, definingDoubleton);
		} else {
			invariantCandidateTerm = EqualityAnalysisResult.notEqualTerm(mScript, definingDoubleton);
		}
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(invariantCandidateTerm, mScript, mSymbolTable);
		final IPredicate invariantCandidate =
				new BasicPredicate(0, tvp.getProcedures(), tvp.getFormula(), tvp.getVars(), tvp.getClosedFormula());
		final Set<IProgramVar> emptyVarSet = Collections.emptySet();
		final IPredicate truePredicate =
				new BasicPredicate(0, new String[0], mScript.term("true"), emptyVarSet, mScript.term("true"));
		final LBool impliedByStem = PredicateUtils.isInductiveHelper(mScript, truePredicate, invariantCandidate,
				mOriginalStem, mModifiableGlobalsAtStart, mModifiableGlobalsAtHonda);
		if (impliedByStem == LBool.UNSAT) {
			final LBool invariantOfLoop = PredicateUtils.isInductiveHelper(mScript, invariantCandidate,
					invariantCandidate, mOriginalLoop, mModifiableGlobalsAtHonda, mModifiableGlobalsAtHonda);
			return invariantOfLoop == LBool.UNSAT;
		}
		return false;
	}

	public EqualityAnalysisResult getEqualityAnalysisResult() {
		return new EqualityAnalysisResult(Collections.unmodifiableSet(mEqualDoubletons),
				Collections.unmodifiableSet(mDistinctDoubletons), Collections.unmodifiableSet(mUnknownDoubletons));
	}

}
