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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class IndexSupportingInvariantAnalysis {
	private final SetOfDoubletons<Term> mAllDoubletons;
	private final Script mScript;
	private final Boogie2SMT mboogie2smt;
	private final ArrayList<Term> mEqualitySupportingInvariants = new ArrayList<Term>();
	private final ArrayList<Term> mNotEqualsSupportingInvariants = new ArrayList<Term>();
	
	private final SetOfDoubletons<Term> distinctDoubletons = new SetOfDoubletons<>();
	private final SetOfDoubletons<Term> equalDoubletons = new SetOfDoubletons<>();
	private final SetOfDoubletons<Term> unknownDoubletons = new SetOfDoubletons<>();
	
	private final TransFormula mOriginalStem;
	private final TransFormula mOriginalLoop;
	private final Set<BoogieVar> mModifiableGlobalsAtStart;
	private final Set<BoogieVar> mModifiableGlobalsAtHonda;
	private final ArrayCellRepVarConstructor mArrayCellRepVarConstructor;
	
	public IndexSupportingInvariantAnalysis(ArrayCellRepVarConstructor arrayCellRepVarConstructor,
			boolean searchAdditionalSupportingInvariants, 
			Boogie2SMT boogie2smt, 
			TransFormula originalStem, TransFormula originalLoop, 
			Set<BoogieVar> modifiableGlobalsAtHonda) {
		super();
		mArrayCellRepVarConstructor = arrayCellRepVarConstructor;
		mboogie2smt = boogie2smt;
		mScript = boogie2smt.getScript();
		mOriginalStem = originalStem;
		mOriginalLoop = originalLoop;
		mModifiableGlobalsAtStart = Collections.emptySet();
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		mAllDoubletons = computeDoubletons();
		
		for (final Doubleton<Term> doubleton : mAllDoubletons.elements()) {
//			if (containsTermVariable(doubleton)) {
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
//			}
		}

	}
	
	
	private void addDistinctDoubleton(Doubleton<Term> doubleton) {
		distinctDoubletons.addDoubleton(doubleton);
		mNotEqualsSupportingInvariants.add(notEqualTerm(doubleton));
	}
	
	private void addEqualDoubleton(Doubleton<Term> doubleton) {
		equalDoubletons.addDoubleton(doubleton);
		mEqualitySupportingInvariants.add(equalTerm(doubleton));
	}
	
	private void addUnknownDoubleton(Doubleton<Term> doubleton) {
		unknownDoubletons.addDoubleton(doubleton);
	}
	
	private SetOfDoubletons<Term> computeDoubletons() {
		final NestedMap2<TermVariable, ArrayIndex, ArrayCellReplacementVarInformation> array2index2repVar = 
				mArrayCellRepVarConstructor.getArrayRepresentative2IndexRepresentative2ReplacementVar();
		final SetOfDoubletons<Term> result = new SetOfDoubletons<>();
		for (final TermVariable array : array2index2repVar.keySet()) {
			final Set<ArrayIndex> allIndices = array2index2repVar.get(array).keySet();
			final ArrayIndex[] allIndicesArr = allIndices.toArray(new ArrayIndex[allIndices.size()]);
			for (int i=0; i<allIndicesArr.length; i++) {
				for (int j=i+1; j<allIndicesArr.length; j++) {
					final List<Term> fstIndex = allIndicesArr[i];
					final List<Term> sndIndex = allIndicesArr[j];
					assert fstIndex.size() == sndIndex.size();
					for (int k=0; k<fstIndex.size(); k++) {
						final Doubleton<Term> Doubleton = new Doubleton<Term>(fstIndex.get(k), sndIndex.get(k));
						result.addDoubleton(Doubleton);
					}
				}
			}
		}
		return result;
	}
	
	
	private Term equalTerm(Doubleton<Term> Doubleton) {
		return SmtUtils.binaryEquality(mScript, Doubleton.getOneElement(), Doubleton.getOtherElement());
	}

	private Term notEqualTerm(Doubleton<Term> Doubleton) {
		return SmtUtils.not(mScript, equalTerm(Doubleton));
	}
	
	private boolean isInVariant(Doubleton<Term> definingDoubleton, boolean checkEquals) {
		Term invariantCandidateTerm;
		if (checkEquals) {
			invariantCandidateTerm = equalTerm(definingDoubleton);
		} else {
			invariantCandidateTerm = notEqualTerm(definingDoubleton);
		}
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(invariantCandidateTerm, mboogie2smt);
		final IPredicate invariantCandidate = new BasicPredicate(0, tvp.getProcedures(), tvp.getFormula(), tvp.getVars(), tvp.getClosedFormula());
		final Set<BoogieVar> emptyVarSet = Collections.emptySet();
		final IPredicate truePredicate = new BasicPredicate(0, new String[0], mScript.term("true"), emptyVarSet, mScript.term("true"));
		final LBool impliedByStem = PredicateUtils.isInductiveHelper(mScript, 
				truePredicate, invariantCandidate, mOriginalStem, mModifiableGlobalsAtStart, mModifiableGlobalsAtHonda);
		if (impliedByStem == LBool.UNSAT) {
			final LBool invariantOfLoop = PredicateUtils.isInductiveHelper(mScript, 
					invariantCandidate, invariantCandidate, mOriginalLoop, mModifiableGlobalsAtHonda, mModifiableGlobalsAtHonda);
			if (invariantOfLoop == LBool.UNSAT) {
				return true;
			} else {
				return false;
			}
		} else {
			return false;
		}
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
	
	public enum Equality { EQUAL, NOT_EQUAL, UNKNOWN };
	
	public boolean isEqualDoubleton(Term t1, Term t2) {
		return equalDoubletons.containsDoubleton(t1, t2);
	}
	
	public boolean isDistinctDoubleton(Term t1, Term t2) {
		return distinctDoubletons.containsDoubleton(t1, t2);
	}
	
	public boolean isUnknownDoubleton(Term t1, Term t2) {
		return unknownDoubletons.containsDoubleton(t1, t2);
	}
	
	public List<Term> getAdditionalConjunctsEqualities() {
		return mEqualitySupportingInvariants;
	}
	
	public List<Term> getAdditionalConjunctsNotEquals() {
		return mNotEqualsSupportingInvariants;
	}
}
