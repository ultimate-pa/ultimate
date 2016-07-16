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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

public class IndexSupportingInvariantAnalysis {
	private final Set<Doubleton<Term>> mAllDoubletons;
	private final Script mScript;
	private final Boogie2SmtSymbolTable mSymbolTable;
	private final ArrayList<Term> mEqualitySupportingInvariants = new ArrayList<Term>();
	private final ArrayList<Term> mNotEqualsSupportingInvariants = new ArrayList<Term>();
	
	private final Set<Doubleton<Term>> mDistinctDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> mEqualDoubletons = new LinkedHashSet<>();
	private final Set<Doubleton<Term>> mUnknownDoubletons = new LinkedHashSet<>();
	
	private final TransFormula mOriginalStem;
	private final TransFormula mOriginalLoop;
	private final Set<BoogieVar> mModifiableGlobalsAtStart;
	private final Set<BoogieVar> mModifiableGlobalsAtHonda;
	
	public IndexSupportingInvariantAnalysis(Set<Doubleton<Term>> allDoubletons,
			Boogie2SmtSymbolTable symbolTable, 
			Script script, 
			TransFormula originalStem,
			TransFormula originalLoop, Set<BoogieVar> modifiableGlobalsAtHonda) {
		super();
		mSymbolTable = symbolTable;
		mScript = script;
		mOriginalStem = originalStem;
		mOriginalLoop = originalLoop;
		mModifiableGlobalsAtStart = Collections.emptySet();
		mModifiableGlobalsAtHonda = modifiableGlobalsAtHonda;
		mAllDoubletons = allDoubletons;

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
	}
	
	
	private void addDistinctDoubleton(Doubleton<Term> doubleton) {
		mDistinctDoubletons.add(doubleton);
		mNotEqualsSupportingInvariants.add(notEqualTerm(doubleton));
	}
	
	private void addEqualDoubleton(Doubleton<Term> doubleton) {
		mEqualDoubletons.add(doubleton);
		mEqualitySupportingInvariants.add(equalTerm(doubleton));
	}
	
	private void addUnknownDoubleton(Doubleton<Term> doubleton) {
		mUnknownDoubletons.add(doubleton);
	}
	

	
	
	private Term equalTerm(Doubleton<Term> doubleton) {
		return SmtUtils.binaryEquality(mScript, doubleton.getOneElement(), doubleton.getOtherElement());
	}

	private Term notEqualTerm(Doubleton<Term> doubleton) {
		return SmtUtils.not(mScript, equalTerm(doubleton));
	}
	
	private boolean isInVariant(Doubleton<Term> definingDoubleton, boolean checkEquals) {
		Term invariantCandidateTerm;
		if (checkEquals) {
			invariantCandidateTerm = equalTerm(definingDoubleton);
		} else {
			invariantCandidateTerm = notEqualTerm(definingDoubleton);
		}
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(invariantCandidateTerm, mScript, mSymbolTable);
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
	
	public enum Equality { EQUAL, NOT_EQUAL, UNKNOWN };
	
	public boolean isEqualDoubleton(Term t1, Term t2) {
		return mEqualDoubletons.contains(new Doubleton<Term>(t1, t2));
	}
	
	public boolean isDistinctDoubleton(Term t1, Term t2) {
		return mDistinctDoubletons.contains(new Doubleton<Term>(t1, t2));
	}
	
	public boolean isUnknownDoubleton(Term t1, Term t2) {
		return mUnknownDoubletons.contains(new Doubleton<Term>(t1, t2));
	}
	
	public List<Term> getAdditionalConjunctsEqualities() {
		return mEqualitySupportingInvariants;
	}
	
	public List<Term> getAdditionalConjunctsNotEquals() {
		return mNotEqualsSupportingInvariants;
	}
}
