/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;

public class IndexSupportingInvariantAnalysis {
	private final SetOfDoubletons<Term> m_AllDoubletons;
	private final Script m_Script;
	private final Boogie2SMT m_boogie2smt;
	private final ArrayList<Term> m_EqualitySupportingInvariants = new ArrayList<Term>();
	private final ArrayList<Term> m_NotEqualsSupportingInvariants = new ArrayList<Term>();;
	
	private final SetOfDoubletons<Term> distinctDoubletons = new SetOfDoubletons<>();
	private final SetOfDoubletons<Term> equalDoubletons = new SetOfDoubletons<>();
	private final SetOfDoubletons<Term> unknownDoubletons = new SetOfDoubletons<>();
	
	private final TransFormula m_OriginalStem;
	private final TransFormula m_OriginalLoop;
	private final ArrayCellRepVarConstructor m_ArrayCellRepVarConstructor;
	
	public IndexSupportingInvariantAnalysis(ArrayCellRepVarConstructor arrayCellRepVarConstructor,
			boolean searchAdditionalSupportingInvariants, 
			Boogie2SMT boogie2smt, 
			TransFormula originalStem, TransFormula originalLoop) {
		super();
		m_ArrayCellRepVarConstructor = arrayCellRepVarConstructor;
		m_boogie2smt = boogie2smt;
		m_Script = boogie2smt.getScript();
		m_OriginalStem = originalStem;
		m_OriginalLoop = originalLoop;
		m_AllDoubletons = computeDoubletons();
		
		for (Doubleton<Term> doubleton : m_AllDoubletons.elements()) {
//			if (containsTermVariable(doubleton)) {
				boolean equalityIsInvariant = isInVariant(doubleton, true);
				if (equalityIsInvariant) {
					addEqualDoubleton(doubleton);
				} else {
					boolean notEqualIsInvariant = isInVariant(doubleton, false);
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
		m_NotEqualsSupportingInvariants.add(notEqualTerm(doubleton));
	}
	
	private void addEqualDoubleton(Doubleton<Term> doubleton) {
		equalDoubletons.addDoubleton(doubleton);
		m_EqualitySupportingInvariants.add(equalTerm(doubleton));
	}
	
	private void addUnknownDoubleton(Doubleton<Term> doubleton) {
		unknownDoubletons.addDoubleton(doubleton);
	}
	
	private SetOfDoubletons<Term> computeDoubletons() {
		NestedMap2<TermVariable, List<Term>, ArrayCellReplacementVarInformation> array2index2repVar = 
				m_ArrayCellRepVarConstructor.getArrayRepresentative2IndexRepresentative2ReplacementVar();
		SetOfDoubletons<Term> result = new SetOfDoubletons<>();
		for (TermVariable array : array2index2repVar.keySet()) {
			Set<List<Term>> allIndices = array2index2repVar.get(array).keySet();
			List<Term>[] allIndicesArr = allIndices.toArray(new List[allIndices.size()]);
			for (int i=0; i<allIndicesArr.length; i++) {
				for (int j=i+1; j<allIndicesArr.length; j++) {
					List<Term> fstIndex = allIndicesArr[i];
					List<Term> sndIndex = allIndicesArr[j];
					assert fstIndex.size() == sndIndex.size();
					for (int k=0; k<fstIndex.size(); k++) {
						Doubleton<Term> Doubleton = new Doubleton<Term>(fstIndex.get(k), sndIndex.get(k));
						result.addDoubleton(Doubleton);
					}
				}
			}
		}
		return result;
	}
	
	
	private Term equalTerm(Doubleton<Term> Doubleton) {
		return SmtUtils.binaryEquality(m_Script, Doubleton.getOneElement(), Doubleton.getOtherElement());
	}

	private Term notEqualTerm(Doubleton<Term> Doubleton) {
		return Util.not(m_Script, equalTerm(Doubleton));
	}
	
	private boolean isInVariant(Doubleton<Term> definingDoubleton, boolean checkEquals) {
		Term invariantCandidateTerm;
		if (checkEquals) {
			invariantCandidateTerm = equalTerm(definingDoubleton);
		} else {
			invariantCandidateTerm = notEqualTerm(definingDoubleton);
		}
		TermVarsProc tvp = TermVarsProc.computeTermVarsProc(invariantCandidateTerm, m_boogie2smt);
		IPredicate invariantCandidate = new BasicPredicate(0, tvp.getProcedures(), tvp.getFormula(), tvp.getVars(), tvp.getClosedFormula());
		Set<BoogieVar> emptyVarSet = Collections.emptySet();
		IPredicate truePredicate = new BasicPredicate(0, new String[0], m_Script.term("true"), emptyVarSet, m_Script.term("true"));
		LBool impliedByStem = PredicateUtils.isInductiveHelper(m_boogie2smt, truePredicate, invariantCandidate, m_OriginalStem);
		if (impliedByStem == LBool.UNSAT) {
			LBool invariantOfLoop = PredicateUtils.isInductiveHelper(m_boogie2smt, invariantCandidate, invariantCandidate, m_OriginalLoop);
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
		return m_EqualitySupportingInvariants;
	}
	
	public List<Term> getAdditionalConjunctsNotEquals() {
		return m_NotEqualsSupportingInvariants;
	}
}
