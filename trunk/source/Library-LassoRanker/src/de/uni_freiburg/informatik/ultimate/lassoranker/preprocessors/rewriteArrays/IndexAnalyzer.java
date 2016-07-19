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

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.util.Utils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class IndexAnalyzer2 {
	private final ILogger mLogger;
	private final boolean mIsStem;
	private final Set<Doubleton<Term>> neitherInvarNorOutvarDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> inVarDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> outVarDoubletons = new LinkedHashSet<>();
	private final Term mTerm;
	private final Script mScript;
	private final Boogie2SMT mboogie2smt;
	private final ReplacementVarFactory mRepvarFactory;
	private final TransFormulaLR mTransFormula;
	
	private final Set<Doubleton<Term>> distinctDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> equalDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> unknownDoubletons = new LinkedHashSet<>();
	/**
	 * Doubletons that we do not check because they do not occur in the formula.
	 */
	private final Set<Doubleton<Term>> ignoredDoubletons = new LinkedHashSet<>();
	
	private final EqualityAnalysisResult mIndexSupportingInvariantAnalysis;
	
	private final boolean mUseArrayIndexSupportingInvariants = true;
	
	public IndexAnalyzer2(Term term, HashRelation<TermVariable, ArrayIndex> array2Indices, 
			Boogie2SMT boogie2smt, TransFormulaLR tf, 
			EqualityAnalysisResult equalityAnalysisAtHonda, boolean isStem, ILogger logger, ReplacementVarFactory replacementVarFactory) {
		super();
		mLogger = logger;
		mIsStem = isStem;
		mTerm = term;
		mboogie2smt = boogie2smt;
		mRepvarFactory = replacementVarFactory;
		mScript = boogie2smt.getScript();
		mTransFormula = tf;
		mIndexSupportingInvariantAnalysis = equalityAnalysisAtHonda;
		analyze(array2Indices);
		mLogger.info(equalDoubletons.size() + " equalDoubletons");
		mLogger.info(distinctDoubletons.size() + " distinctDoubletons");
		mLogger.info(unknownDoubletons.size() + " unknownDoubletons");
		mLogger.info(ignoredDoubletons.size() + " ignoredDoubletons");
	}
	
	
	private void addDistinctDoubleton(Doubleton<Term> doubleton) {
		distinctDoubletons.add(doubleton);
	}
	
	private void addEqualDoubleton(Doubleton<Term> doubleton) {
		equalDoubletons.add(doubleton);
	}
	
	private void addUnknownDoubleton(Doubleton<Term> doubleton) {
		unknownDoubletons.add(doubleton);
	}
	
	private void analyze(HashRelation<TermVariable, ArrayIndex> array2Indices) {
		Term termWithAdditionalInvariants;
		if (mUseArrayIndexSupportingInvariants && !mIsStem) {
			final Term equalitiesOriginal = SmtUtils.and(mScript, mIndexSupportingInvariantAnalysis.constructListOfEqualities(mScript));
			final Term notequalsOriginal = SmtUtils.and(mScript, mIndexSupportingInvariantAnalysis.constructListOfNotEquals(mScript));
			final Term equalitiesRenamed = TransFormulaUtils.translateTermVariablesToInVars(mScript, 
					mTransFormula, equalitiesOriginal, mboogie2smt.getBoogie2SmtSymbolTable(), mRepvarFactory);
			final Term notequalsRenamed = TransFormulaUtils.translateTermVariablesToInVars(mScript, 
					mTransFormula, notequalsOriginal, mboogie2smt.getBoogie2SmtSymbolTable(), mRepvarFactory);
			termWithAdditionalInvariants = Util.and(mScript, mTerm, equalitiesRenamed, notequalsRenamed);
		} else {
			termWithAdditionalInvariants = mTerm;
		}
 		final Set<TermVariable> varsInTerm = new HashSet<>(Arrays.asList(termWithAdditionalInvariants.getFreeVars()));
		
		for (final TermVariable tv : array2Indices.getDomain()) {
			final Set<ArrayIndex> test = array2Indices.getImage(tv);
			final ArrayIndex[] testArr = test.toArray(new ArrayIndex[test.size()]);
			for (int i=0; i<testArr.length; i++) {
				for (int j=i+1; j<testArr.length; j++) {
					final ArrayIndex fstIndex = testArr[i];
					final ArrayIndex sndIndex = testArr[j];
					assert fstIndex.size() == sndIndex.size();
					if (fstIndex.freeVarsAreSubset(varsInTerm) && sndIndex.freeVarsAreSubset(varsInTerm)) {
						final boolean isInvarPair = isInvarPair(fstIndex, sndIndex);
						final boolean isOutvarPair = isOutvarPair(fstIndex, sndIndex);
						for (int k=0; k<fstIndex.size(); k++) {
							markForComparison(fstIndex.get(k), sndIndex.get(k), isInvarPair, isOutvarPair);
						}
					} else {
						for (int k=0; k<fstIndex.size(); k++) {
							ignoredDoubletons.add(new Doubleton<Term>(fstIndex.get(k), sndIndex.get(k)));
						}
					}
				}
			}
		}
		if (!mIsStem) {
			processDoubletonsWithArrayIndexInvariants(inVarDoubletons);
		}
		processDoubletonsWithArrayIndexInvariants(outVarDoubletons);
		

		if (mIsStem) {
			processDoubletonsWithOwnAnalysis(inVarDoubletons, termWithAdditionalInvariants);
		} else {
			// there are equal outVar doubletons that are not loop invariants
			// because they are not established by the stem.
			// e.g., while (*) { x:=1, y:=1 }
			processDoubletonsWithOwnAnalysis(outVarDoubletons, termWithAdditionalInvariants);
		}
		processDoubletonsWithOwnAnalysis(neitherInvarNorOutvarDoubletons, termWithAdditionalInvariants);
	}



	private boolean isInvarPair(ArrayIndex fstIndex, ArrayIndex sndIndex) {
		final boolean fstIndexIsInvarIndex = 
				TransFormulaUtils.allVariablesAreInVars(fstIndex, mTransFormula);
		final boolean sndIndexIsInvarIndex = 
				TransFormulaUtils.allVariablesAreInVars(sndIndex, mTransFormula);
		final boolean isInvarPair = fstIndexIsInvarIndex && sndIndexIsInvarIndex;
		return isInvarPair;
	}
	
	private boolean isOutvarPair(ArrayIndex fstIndex, ArrayIndex sndIndex) {
		final boolean fstIndexIsOutvarIndex = 
				TransFormulaUtils.allVariablesAreOutVars(fstIndex, mTransFormula);
		final boolean sndIndexIsOutvarIndex = 
				TransFormulaUtils.allVariablesAreOutVars(sndIndex, mTransFormula);
		final boolean isOutvarPair = fstIndexIsOutvarIndex && sndIndexIsOutvarIndex;
		return isOutvarPair;
	}



	private void processDoubletonsWithOwnAnalysis(Set<Doubleton<Term>> doubletons, Term termWithAdditionalInvariants) {
		mScript.push(1);
		final Set<TermVariable> allTvs = new HashSet<>(Arrays.asList(termWithAdditionalInvariants.getFreeVars()));
		allTvs.addAll(Utils.filter(mTransFormula.getInVarsReverseMapping().keySet(), TermVariable.class));
		allTvs.addAll(Utils.filter(mTransFormula.getOutVarsReverseMapping().keySet(), TermVariable.class));
		final Map<Term, Term> substitutionMapping = SmtUtils.termVariables2Constants(mScript, mboogie2smt.getVariableManager(), allTvs);
		final SafeSubstitution subst = new SafeSubstitution(mScript, substitutionMapping);
		mScript.assertTerm(subst.transform(termWithAdditionalInvariants));
		for (final Doubleton<Term> doubleton : doubletons) {
			//todo ignore doubletons that are already there
			final Term equal = subst.transform(
					SmtUtils.binaryEquality(mScript, 
							doubleton.getOneElement(), doubleton.getOtherElement()));
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
		}
		mScript.pop(1);
	}
	


	private void processDoubletonsWithArrayIndexInvariants(Set<Doubleton<Term>> doubletons) {
		for (final Doubleton<Term> doubleton : doubletons) {
			final Doubleton<Term> definingDoubleton = constructDefiningDoubleton(doubleton);
			if (definingDoubleton.getOneElement() == definingDoubleton.getOtherElement()) {
				// trivially equal
				addEqualDoubleton(doubleton);
			} else if (mIndexSupportingInvariantAnalysis.getEqualDoubletons().contains(definingDoubleton)) {
				addEqualDoubleton(doubleton);
			} else if (mIndexSupportingInvariantAnalysis.getDistinctDoubletons().contains(definingDoubleton)) {
				addDistinctDoubleton(doubleton);
			} else if (mIndexSupportingInvariantAnalysis.getUnknownDoubletons().contains(definingDoubleton)) {
				addUnknownDoubleton(doubleton);
			} else {
				throw new AssertionError("inVar (or outVar) doulbeton has to be in invariant anlysis");
			}
		}
		
	}

	private Doubleton<Term> constructDefiningDoubleton(Doubleton<Term> inVarDoubleton) {
		final Term oneElement = inVarDoubleton.getOneElement();
		final Term otherElement = inVarDoubleton.getOtherElement();
		final Term translatedOne = TransFormulaUtils.translateTermVariablesToDefinitions(
				mScript, mTransFormula, oneElement);
		final Term translatedOther = TransFormulaUtils.translateTermVariablesToDefinitions(
				mScript, mTransFormula, otherElement);
		return new Doubleton<Term>(translatedOne, translatedOther);
		
	}
	
	private boolean containsTermVariable(Doubleton<Term> Doubleton) {
		if (Doubleton.getOneElement().getFreeVars().length > 0) {
			return true;
		} else if (Doubleton.getOtherElement().getFreeVars().length > 0) {
			return true;
		} else {
			return false;
		}
	}
	
	private void markForComparison(Term term1, Term term2, boolean isInvarPair, boolean isOutvarPair) {
//		if (term1 == term2) {
//			// do nothing, omit this pair
//		} else {
			final Doubleton<Term> doubleton = new Doubleton<Term>(term1, term2);
			if (isInvarPair) {
				inVarDoubletons.add(doubleton);
			} 
			if (isOutvarPair) {
				outVarDoubletons.add(doubleton);
			} 
			if (!isInvarPair && !isOutvarPair) {
				neitherInvarNorOutvarDoubletons.add(doubleton);
			}
//		}
	}
	
	
	public IndexAnalysisResult getResult() {
		return new IndexAnalysisResult(
				Collections.unmodifiableSet(equalDoubletons),
				Collections.unmodifiableSet(distinctDoubletons),
				Collections.unmodifiableSet(unknownDoubletons),
				Collections.unmodifiableSet(ignoredDoubletons));
	}
}
