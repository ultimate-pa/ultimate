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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Analyze for a given {@link ModifiableTransFormula} and mapping from arrays to their indices which pairs of index
 * entries are equal or distinct. The analysis can benefit from additional invariants that hold before this
 * {@link ModifiableTransFormula} and from from additional invariants that hold after this
 * {@link ModifiableTransFormula}. the additional invariants are each given as EqualityAnalysisResult.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IndexAnalyzer {
	private final ILogger mLogger;
	private final Term mTerm;
	private final Script mScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final ReplacementVarFactory mRepvarFactory;
	private final ModifiableTransFormula mTransFormula;

	private final Set<Doubleton<Term>> mDistinctDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> mEqualDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> mUnknownDoubletons = new LinkedHashSet<>();
	/**
	 * Doubletons that we do not check because they do not occur in the formula.
	 */
	private final Set<Doubleton<Term>> mIgnoredDoubletons = new LinkedHashSet<>();

	private final EqualityAnalysisResult mInvariantEqualitiesBefore;
	private final EqualityAnalysisResult mInvariantEqualitiesAfter;

	private final boolean mUseArrayIndexSupportingInvariants = true;

	public IndexAnalyzer(final Term term, final Set<Doubleton<Term>> doubletons, final IIcfgSymbolTable symbolTable,
			final ModifiableTransFormula tf, final EqualityAnalysisResult invariantEqualitiesBefore,
			final EqualityAnalysisResult invariantEqualitiesAfter, final ILogger logger,
			final ReplacementVarFactory replacementVarFactory, final ManagedScript mgdScript) {
		super();
		mLogger = logger;
		mTerm = term;
		mSymbolTable = symbolTable;
		mRepvarFactory = replacementVarFactory;
		mScript = mgdScript.getScript();
		mTransFormula = tf;
		mInvariantEqualitiesBefore = invariantEqualitiesBefore;
		mInvariantEqualitiesAfter = invariantEqualitiesAfter;
		final Set<Doubleton<Term>> allDoubletons = doubletons;
		final Set<Doubleton<Term>> remainingDoubletons = preprocessWithInvariants(allDoubletons);

		Term termWithAdditionalInvariants;
		if (mUseArrayIndexSupportingInvariants) {
			final Term equalitiesOriginal =
					SmtUtils.and(mScript, mInvariantEqualitiesBefore.constructListOfEqualities(mScript));
			final Term notequalsOriginal =
					SmtUtils.and(mScript, mInvariantEqualitiesBefore.constructListOfNotEquals(mScript));
			final Term equalitiesRenamed = ModifiableTransFormulaUtils.translateTermVariablesToInVars(mScript,
					mTransFormula, equalitiesOriginal, mSymbolTable, mRepvarFactory);
			final Term notequalsRenamed = ModifiableTransFormulaUtils.translateTermVariablesToInVars(mScript,
					mTransFormula, notequalsOriginal, mSymbolTable, mRepvarFactory);
			termWithAdditionalInvariants = SmtUtils.and(mScript, mTerm, equalitiesRenamed, notequalsRenamed);
		} else {
			termWithAdditionalInvariants = mTerm;
		}

		processDoubletonsWithOwnAnalysis(remainingDoubletons, termWithAdditionalInvariants);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Indices for " + tf.getFormula());
			if (!mEqualDoubletons.isEmpty() || !mDistinctDoubletons.isEmpty() || !mUnknownDoubletons.isEmpty()
					|| !mIgnoredDoubletons.isEmpty()) {
				mLogger.debug(mEqualDoubletons.size() + " equalDoubletons");
				mLogger.debug(mDistinctDoubletons.size() + " distinctDoubletons");
				mLogger.debug(mUnknownDoubletons.size() + " unknownDoubletons");
				mLogger.debug(mIgnoredDoubletons.size() + " ignoredDoubletons");
			} else {
				mLogger.debug("No Doubletons");
			}
		}
	}

	// TODO: This constructor is only used by the old map-elimination!
	public IndexAnalyzer(final Term formula, final HashRelation<Term, ArrayIndex> arrays2Indices,
			final IIcfgSymbolTable boogie2SmtSymbolTable, final ModifiableTransFormula tf,
			final EqualityAnalysisResult invariantEqualitiesBefore,
			final EqualityAnalysisResult invariantEqualitiesAfter, final ILogger logger,
			final ReplacementVarFactory replacementVarFactory, final ManagedScript mgdScript) {
		this(formula, extractDoubletons(arrays2Indices), boogie2SmtSymbolTable, tf, invariantEqualitiesBefore,
				invariantEqualitiesAfter, logger, replacementVarFactory, mgdScript);
	}

	private Set<Doubleton<Term>> preprocessWithInvariants(final Set<Doubleton<Term>> allDoubletons) {
		final Set<Doubleton<Term>> result = new HashSet<>();
		for (final Doubleton<Term> doubleton : allDoubletons) {
			if (isInVarDoubleton(doubleton)) {
				gradeDoubleton(doubleton, mInvariantEqualitiesBefore, mEqualDoubletons, mDistinctDoubletons, result);
			} else if (isOutVarDoubleton(doubleton)) {
				gradeDoubleton(doubleton, mInvariantEqualitiesAfter, mEqualDoubletons, mDistinctDoubletons, result);
			} else {
				result.add(doubleton);
			}
		}
		return result;
	}

	private void gradeDoubleton(final Doubleton<Term> doubleton, final EqualityAnalysisResult invariantEqualities,
			final Set<Doubleton<Term>> equalDoubletons, final Set<Doubleton<Term>> distinctDoubletons,
			final Set<Doubleton<Term>> furtherAnalysisRequired) throws AssertionError {
		final Doubleton<Term> definingDoubleton = constructDefiningDoubleton(doubleton);
		final EqualityStatus equalityStatus;
		try {
			equalityStatus = invariantEqualities.getEqualityStatus(definingDoubleton);
		} catch (final IllegalArgumentException e) {
			// TODO: Find out why we do not have all Doubletons in invariant analysis
			furtherAnalysisRequired.add(doubleton);
			return;
		}
		switch (equalityStatus) {
		case EQUAL:
			equalDoubletons.add(doubleton);
			break;
		case NOT_EQUAL:
			distinctDoubletons.add(doubleton);
			break;
		case UNKNOWN:
			// further analysis required because
			// there are equal outVar doubletons that are not loop invariants
			// because they are not established by the stem.
			// e.g., while (*) { x:=1, y:=1 }
			furtherAnalysisRequired.add(doubleton);
			break;
		default:
			throw new AssertionError();
		}
	}

	private boolean isInVarDoubleton(final Doubleton<Term> doubleton) {
		final boolean fstIndexIsInvarIndex =
				ModifiableTransFormulaUtils.allVariablesAreInVars(doubleton.getOneElement(), mTransFormula);
		final boolean sndIndexIsInvarIndex =
				ModifiableTransFormulaUtils.allVariablesAreInVars(doubleton.getOtherElement(), mTransFormula);
		final boolean isInvarPair = fstIndexIsInvarIndex && sndIndexIsInvarIndex;
		return isInvarPair;
	}

	private boolean isOutVarDoubleton(final Doubleton<Term> doubleton) {
		final boolean fstIndexIsOutvarIndex =
				ModifiableTransFormulaUtils.allVariablesAreOutVars(doubleton.getOneElement(), mTransFormula);
		final boolean sndIndexIsOutvarIndex =
				ModifiableTransFormulaUtils.allVariablesAreOutVars(doubleton.getOtherElement(), mTransFormula);
		final boolean isOutvarPair = fstIndexIsOutvarIndex && sndIndexIsOutvarIndex;
		return isOutvarPair;
	}

	private static Set<Doubleton<Term>> extractDoubletons(final HashRelation<Term, ArrayIndex> array2Indices) {
		final Set<Doubleton<Term>> result = new HashSet<>();
		for (final Term tv : array2Indices.getDomain()) {
			final Set<ArrayIndex> test = array2Indices.getImage(tv);
			final ArrayIndex[] testArr = test.toArray(new ArrayIndex[test.size()]);
			for (int i = 0; i < testArr.length; i++) {
				for (int j = i + 1; j < testArr.length; j++) {
					final ArrayIndex fstIndex = testArr[i];
					final ArrayIndex sndIndex = testArr[j];
					assert fstIndex.size() == sndIndex.size() : "incompatible size";
					for (int k = 0; k < fstIndex.size(); k++) {
						result.add(new Doubleton<>(fstIndex.get(k), sndIndex.get(k)));
					}
				}
			}
		}
		return result;
	}

	private void addDistinctDoubleton(final Doubleton<Term> doubleton) {
		mDistinctDoubletons.add(doubleton);
		// if (isInVarDoubleton(doubleton)) {
		// throw new AssertionError("old analysis not perfect inVar");
		// }
		// if (isInVarDoubleton(doubleton)) {
		// throw new AssertionError("old analysis not perfect outVar");
		// }
	}

	private void addEqualDoubleton(final Doubleton<Term> doubleton) {
		mEqualDoubletons.add(doubleton);
		// if (isInVarDoubleton(doubleton)) {
		// throw new AssertionError("old analysis not perfect inVar");
		// }
		// if (isInVarDoubleton(doubleton)) {
		// throw new AssertionError("old analysis not perfect outVar");
		// }
	}

	private void addUnknownDoubleton(final Doubleton<Term> doubleton) {
		mUnknownDoubletons.add(doubleton);
	}

	private void processDoubletonsWithOwnAnalysis(final Set<Doubleton<Term>> doubletons,
			final Term termWithAdditionalInvariants) {
		mScript.echo(new QuotedObject("starting index analysis for TransFormula"));
		mScript.push(1);
		final Set<TermVariable> allTvs = new HashSet<>(Arrays.asList(termWithAdditionalInvariants.getFreeVars()));
		allTvs.addAll(CoreUtil.filter(mTransFormula.getInVarsReverseMapping().keySet(), TermVariable.class));
		allTvs.addAll(CoreUtil.filter(mTransFormula.getOutVarsReverseMapping().keySet(), TermVariable.class));
		final Map<TermVariable, Term> substitutionMapping = SmtUtils.termVariables2Constants(mScript, allTvs, true);
		final Substitution subst = new Substitution(mScript, substitutionMapping);
		mScript.assertTerm(subst.transform(termWithAdditionalInvariants));
		for (final Doubleton<Term> doubleton : doubletons) {
			if (allVarsOccurInFormula(doubleton, termWithAdditionalInvariants)) {
				// todo ignore doubletons that are already there
				final Term equal = subst.transform(
						SmtUtils.binaryEquality(mScript, doubleton.getOneElement(), doubleton.getOtherElement()));
				mScript.push(1);
				mScript.assertTerm(equal);
				LBool lbool = mScript.checkSat();
				mScript.pop(1);
				if (lbool == LBool.UNSAT) {
					addDistinctDoubleton(doubleton);
				} else {
					final Term notEqual = SmtUtils.not(mScript, equal);
					mScript.push(1);
					mScript.assertTerm(notEqual);
					lbool = mScript.checkSat();
					mScript.pop(1);
					if (lbool == LBool.UNSAT) {
						addEqualDoubleton(doubleton);
					} else {
						addUnknownDoubleton(doubleton);
					}
				}
			} else {
				mIgnoredDoubletons.add(doubleton);
			}
		}
		mScript.pop(1);
		mScript.echo(new QuotedObject("finished index analysis for TransFormula"));
	}

	private boolean allVarsOccurInFormula(final Doubleton<Term> doubleton, final Term termWithAdditionalInvariants) {
		final Set<TermVariable> freeVarsInDoubleton = new HashSet();
		freeVarsInDoubleton.addAll(Arrays.asList(doubleton.getOneElement().getFreeVars()));
		freeVarsInDoubleton.addAll(Arrays.asList(doubleton.getOtherElement().getFreeVars()));
		final Set<TermVariable> freeVarsInFormula =
				new HashSet(Arrays.asList(termWithAdditionalInvariants.getFreeVars()));
		return freeVarsInFormula.containsAll(freeVarsInDoubleton);
	}

	private Doubleton<Term> constructDefiningDoubleton(final Doubleton<Term> inVarDoubleton) {
		final Term oneElement = inVarDoubleton.getOneElement();
		final Term otherElement = inVarDoubleton.getOtherElement();
		final Term translatedOne =
				ModifiableTransFormulaUtils.translateTermVariablesToDefinitions(mScript, mTransFormula, oneElement);
		final Term translatedOther =
				ModifiableTransFormulaUtils.translateTermVariablesToDefinitions(mScript, mTransFormula, otherElement);
		return new Doubleton<>(translatedOne, translatedOther);

	}

	private boolean containsTermVariable(final Doubleton<Term> Doubleton) {
		if (Doubleton.getOneElement().getFreeVars().length > 0) {
			return true;
		}
		return Doubleton.getOtherElement().getFreeVars().length > 0;
	}

	public IndexAnalysisResult getResult() {
		return new IndexAnalysisResult(Collections.unmodifiableSet(mEqualDoubletons),
				Collections.unmodifiableSet(mDistinctDoubletons), Collections.unmodifiableSet(mUnknownDoubletons),
				Collections.unmodifiableSet(mIgnoredDoubletons));
	}
}
