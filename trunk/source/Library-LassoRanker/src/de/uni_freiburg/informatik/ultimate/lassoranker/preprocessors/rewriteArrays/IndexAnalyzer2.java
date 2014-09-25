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
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteArrays;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.Utils;

public class IndexAnalyzer2 {
	private final SetOfDoubletons<Term> nonInvarDoubletons = new SetOfDoubletons<>();
	private final SetOfDoubletons<Term> inVarDoubletons = new SetOfDoubletons<>();
	private final Term m_Term;
	private final Script m_Script;
	private final Boogie2SMT m_boogie2smt;
	private final TransFormulaLR m_TransFormula;
	private final ArrayList<Term> m_AdditionalEqualities;
	private final ArrayList<Term> m_AdditionalNotequals;
	
	private final SetOfDoubletons<Term> distinctDoubletons = new SetOfDoubletons<>();
	private final SetOfDoubletons<Term> equalDoubletons = new SetOfDoubletons<>();
	private final SetOfDoubletons<Term> unknownDoubletons = new SetOfDoubletons<>();
	
	private final IndexSupportingInvariantAnalysis m_IndexSupportingInvariantAnalysis;
	
	private final boolean m_SearchAdditionalSupportingInvariants = true;
	
	public IndexAnalyzer2(Term term, HashRelation<TermVariable, 
			List<Term>> array2Indices, 
			Boogie2SMT boogie2smt, TransFormulaLR tf, 
			IndexSupportingInvariantAnalysis indexSupportingInvariantAnalysis) {
		super();
		m_Term = term;
		m_boogie2smt = boogie2smt;
		m_Script = boogie2smt.getScript();
		m_TransFormula = tf;
		m_IndexSupportingInvariantAnalysis = indexSupportingInvariantAnalysis;
		m_AdditionalEqualities = new ArrayList<>();
		m_AdditionalNotequals = new ArrayList<>();
		analyze(array2Indices);
	}
	
	
	private void addDistinctDoubleton(Doubleton<Term> doubleton) {
		distinctDoubletons.addDoubleton(doubleton);
		m_AdditionalNotequals.add(notEqualTerm(doubleton));
	}
	
	private void addEqualDoubleton(Doubleton<Term> doubleton) {
		equalDoubletons.addDoubleton(doubleton);
		m_AdditionalEqualities.add(equalTerm(doubleton));
	}
	
	private void addUnknownDoubleton(Doubleton<Term> doubleton) {
		unknownDoubletons.addDoubleton(doubleton);
	}
	
	void analyze(HashRelation<TermVariable, List<Term>> array2Indices) { 
		for (TermVariable tv : array2Indices.getDomain()) {
			Set<List<Term>> test = array2Indices.getImage(tv);
			List<Term>[] testArr = test.toArray(new List[test.size()]);
			for (int i=0; i<testArr.length; i++) {
				for (int j=i+1; j<testArr.length; j++) {
					List<Term> fstIndex = testArr[i];
					List<Term> sndIndex = testArr[j];
					assert fstIndex.size() == sndIndex.size();
					boolean fstIndexIsInvarIndex = 
								RewriteArrays.allVariablesAreInVars(fstIndex, m_TransFormula);
					boolean sndIndexIsInvarIndexOrOutVarIndex = 
								RewriteArrays.allVariablesAreInVars(sndIndex, m_TransFormula);
					boolean isInvarPair = fstIndexIsInvarIndex && 
								sndIndexIsInvarIndexOrOutVarIndex;
					for (int k=0; k<fstIndex.size(); k++) {
						markForComparison(fstIndex.get(k), sndIndex.get(k), isInvarPair);
					}
				}
			}
		}
		
		processInVarDoubletons();
		
		Term termWithAdditionalInvariants;
		
		if (m_SearchAdditionalSupportingInvariants) { 
			termWithAdditionalInvariants = Util.and(m_Script, m_Term, getAdditionalConjunctsEqualities(), getAdditionalConjunctsNotEquals());
		} else {
			termWithAdditionalInvariants = m_Term;
		}

		processNonInvarDoubletons(termWithAdditionalInvariants);
	}


	private void processNonInvarDoubletons(Term termWithAdditionalInvariants) {
		m_Script.push(1);
		Set<TermVariable> allTvs = new HashSet<>(Arrays.asList(termWithAdditionalInvariants.getFreeVars()));
		allTvs.addAll(Utils.filter(m_TransFormula.getInVarsReverseMapping().keySet(), TermVariable.class));
		allTvs.addAll(Utils.filter(m_TransFormula.getOutVarsReverseMapping().keySet(), TermVariable.class));
		Map<Term, Term> substitutionMapping = SmtUtils.termVariables2Constants(m_Script, m_boogie2smt.getVariableManager(), allTvs);
		SafeSubstitution subst = new SafeSubstitution(m_Script, substitutionMapping);
		m_Script.assertTerm(subst.transform(termWithAdditionalInvariants));
		for (Doubleton<Term> Doubleton : nonInvarDoubletons.elements()) {
			//todo ignore doubletons that are already there
			Term equal = subst.transform(
					SmtUtils.binaryEquality(m_Script, 
							Doubleton.getOneElement(), Doubleton.getOtherElement()));
			m_Script.push(1);
			m_Script.assertTerm(equal);
			LBool lbool = m_Script.checkSat();
			m_Script.pop(1);
			if (lbool == LBool.UNSAT) {
				addDistinctDoubleton(Doubleton);
			} else {
				Term notEqual = Util.not(m_Script, equal);
				m_Script.push(1);
				m_Script.assertTerm(notEqual);
				lbool = m_Script.checkSat();
				m_Script.pop(1);
				if (lbool == LBool.UNSAT) {
					addEqualDoubleton(Doubleton);
				} else {
					addUnknownDoubleton(Doubleton);
				}
			}
		}
		m_Script.pop(1);
	}
	


	private void processInVarDoubletons() {
		for (Doubleton<Term> doubleton : inVarDoubletons.elements()) {
			Doubleton<Term> definingDoubleton = constructDefiningDoubleton(doubleton);
			if (definingDoubleton.getOneElement() == definingDoubleton.getOtherElement()) {
				// trivially equal
				addEqualDoubleton(doubleton);
			} else if (m_IndexSupportingInvariantAnalysis.isEqualDoubleton(definingDoubleton.getOneElement(), definingDoubleton.getOtherElement())) {
				addEqualDoubleton(doubleton);
			} else if (m_IndexSupportingInvariantAnalysis.isDistinctDoubleton(definingDoubleton.getOneElement(), definingDoubleton.getOtherElement())) {
				addDistinctDoubleton(doubleton);
			} else if (m_IndexSupportingInvariantAnalysis.isUnknownDoubleton(definingDoubleton.getOneElement(), definingDoubleton.getOtherElement())) {
				addUnknownDoubleton(doubleton);
			} else {
				throw new AssertionError("inVar doulbeton has to be in invariant anlysis");
			}
		}
		
	}


	private Term equalTerm(Doubleton<Term> Doubleton) {
		return SmtUtils.binaryEquality(m_Script, Doubleton.getOneElement(), Doubleton.getOtherElement());
	}

	private Term notEqualTerm(Doubleton<Term> Doubleton) {
		return Util.not(m_Script, equalTerm(Doubleton));
	}
	
	
	private Doubleton<Term> constructDefiningDoubleton(Doubleton<Term> inVarDoubleton) {
		Term oneElement = inVarDoubleton.getOneElement();
		Term otherElement = inVarDoubleton.getOtherElement();
		Term[] translatedOne = RewriteArrays.translateTermVariablesToDefinitions(
				m_Script, m_TransFormula, oneElement);
		assert translatedOne.length == 1;
		Term[] translatedOther = RewriteArrays.translateTermVariablesToDefinitions(
				m_Script, m_TransFormula, otherElement);
		assert translatedOther.length == 1;
		return new Doubleton<Term>(translatedOne[0], translatedOther[0]);
		
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
	
	private void markForComparison(Term term1, Term term2, boolean isInvarOrOutvarPair) {
//		if (term1 == term2) {
//			// do nothing, omit this pair
//		} else {
			Doubleton<Term> Doubleton = new Doubleton<Term>(term1, term2);
			if (isInvarOrOutvarPair) {
				inVarDoubletons.addDoubleton(Doubleton);
			} else {
				nonInvarDoubletons.addDoubleton(Doubleton);
			}
//		}
	}
	
	public enum Equality { EQUAL, NOT_EQUAL, UNKNOWN };
	
	public Equality isEqual(List<Term> index1, List<Term> index2) {
		assert index1.size() == index2.size();
		boolean oneEntryWasUnknown = false;
		for (int i=0; i<index1.size(); i++) {
			if (index1.get(i) == index2.get(i)) {
				continue;
			}
			if (isDistinctDoubleton(index1.get(i), index2.get(i))) {
				return Equality.NOT_EQUAL;
			}
			if (isUnknownDoubleton(index1.get(i), index2.get(i))) {
				oneEntryWasUnknown = true;
			} else {
				assert (isEqualDoubleton(index1.get(i), index2.get(i)));
			}
		}
		if (oneEntryWasUnknown) {
			return Equality.UNKNOWN;
		} else {
			return Equality.EQUAL;
		}
	}
	
	public boolean isEqualDoubleton(Term t1, Term t2) {
		return equalDoubletons.containsDoubleton(t1, t2);
	}
	
	public boolean isDistinctDoubleton(Term t1, Term t2) {
		return distinctDoubletons.containsDoubleton(t1, t2);
	}
	
	public boolean isUnknownDoubleton(Term t1, Term t2) {
		return unknownDoubletons.containsDoubleton(t1, t2);
	}

	public Term getAdditionalConjunctsEqualities() {
		return Util.and(m_Script, m_AdditionalEqualities.toArray(new Term[m_AdditionalEqualities.size()]));
	}
	
	public Term getAdditionalConjunctsNotEquals() {
		return Util.and(m_Script, m_AdditionalNotequals.toArray(new Term[m_AdditionalNotequals.size()]));
	}
}
