package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteArrays;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

public class IndexAnalyzer {
	private final SetOfTwoeltons<Term> allTwoeltons = new SetOfTwoeltons<>();
	private final SetOfTwoeltons<Term> inVarTwoeltons = new SetOfTwoeltons<>();
	private final Term m_Term;
	private final Script m_Script;
	private final Boogie2SMT m_boogie2smt;
	private final VarCollector m_VarCollector;
	private final Collection<Term> m_SupportingInvariants;
	private final ArrayList<Object> m_AdditionalEqualities;
	private final ArrayList<Object> m_AdditionalNotequals;
	
	private final SetOfTwoeltons<Term> distinctTwoeltons = new SetOfTwoeltons<>();
	private final SetOfTwoeltons<Term> equalTwoeltons = new SetOfTwoeltons<>();
	private final SetOfTwoeltons<Term> unknownTwoeltons = new SetOfTwoeltons<>();
	private final TransFormula m_OriginalStem;
	private final TransFormula m_OriginalLoop;

	
	
	public IndexAnalyzer(Term term, HashRelation<TermVariable, 
			List<Term>> array2Indices, Boogie2SMT boogie2smt, VarCollector varCollector, 
			TransFormula originalStem, TransFormula originalLoop) {
		super();
		m_Term = term;
		m_boogie2smt = boogie2smt;
		m_Script = boogie2smt.getScript();
		m_VarCollector = varCollector;
		m_SupportingInvariants = new ArrayList<>();
		m_AdditionalEqualities = new ArrayList<>();
		m_AdditionalNotequals = new ArrayList<>();
		m_OriginalStem = originalStem;
		m_OriginalLoop = originalLoop;
		analyze(array2Indices);
	}
	
	
	private void addDistinctDoubleton(Twoelton<Term> doubleton) {
		distinctTwoeltons.addTowelton(doubleton);
		m_AdditionalNotequals.add(notEqualTerm(doubleton));
	}
	
	private void addEqualDoubleton(Twoelton<Term> doubleton) {
		equalTwoeltons.addTowelton(doubleton);
		m_AdditionalEqualities.add(equalTerm(doubleton));
	}
	
	private void addUnknownDoubleton(Twoelton<Term> doubleton) {
		unknownTwoeltons.addTowelton(doubleton);
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
					for (int k=0; k<fstIndex.size(); k++) {
						markForComparison(fstIndex.get(k), sndIndex.get(k));
					}
				}
			}
		}
		
		for (Twoelton<Term> inVarTwoelton : inVarTwoeltons.elements()) {
			if (containsTermVariable(inVarTwoelton)) {
				Twoelton<Term> definingTwoelton = constructDefiningTwoelton(inVarTwoelton);
				boolean equalityIsInvariant = isInVariant(definingTwoelton, true);
				if (equalityIsInvariant) {
					m_SupportingInvariants.add(equalTerm(definingTwoelton));
					addEqualDoubleton(inVarTwoelton);
				} else {
					boolean notEqualIsInvariant = isInVariant(definingTwoelton, false);
					if (notEqualIsInvariant) {
						m_SupportingInvariants.add(notEqualTerm(definingTwoelton));
						addDistinctDoubleton(inVarTwoelton);
					} else {
						addUnknownDoubleton(inVarTwoelton);
					}
				} 
			}
			
		}
		Term termWithAdditionalInvariants = Util.and(m_Script, m_Term, getAdditionalConjunctsEqualities());

		m_Script.push(1);
		Map<Term, Term> substitutionMapping = SmtUtils.termVariables2Constants(m_Script, m_boogie2smt.getVariableManager(), termWithAdditionalInvariants.getFreeVars());
		SafeSubstitution subst = new SafeSubstitution(m_Script, substitutionMapping);
		m_Script.assertTerm(subst.transform(termWithAdditionalInvariants));
		for (Twoelton<Term> twoelton : allTwoeltons.elements()) {
			//todo ignore toweltons that are already there
			Term equal = subst.transform(
					SmtUtils.binaryEquality(m_Script, 
							twoelton.getOneElement(), twoelton.getOtherElement()));
			m_Script.push(1);
			m_Script.assertTerm(equal);
			LBool lbool = m_Script.checkSat();
			m_Script.pop(1);
			if (lbool == LBool.UNSAT) {
				addDistinctDoubleton(twoelton);
			} else {
				Term notEqual = Util.not(m_Script, equal);
				m_Script.push(1);
				m_Script.assertTerm(notEqual);
				lbool = m_Script.checkSat();
				m_Script.pop(1);
				if (lbool == LBool.UNSAT) {
					addEqualDoubleton(twoelton);
				} else {
					addUnknownDoubleton(twoelton);
				}
			}
		}
		m_Script.pop(1);
	}
	
	private Term equalTerm(Twoelton<Term> twoelton) {
		return SmtUtils.binaryEquality(m_Script, twoelton.getOneElement(), twoelton.getOtherElement());
	}

	private Term notEqualTerm(Twoelton<Term> twoelton) {
		return Util.not(m_Script, equalTerm(twoelton));
	}

	

	private boolean isInVariant(Twoelton<Term> definingTwoelton, boolean checkEquals) {
		Term invariantCandidateTerm;
		if (checkEquals) {
			invariantCandidateTerm = equalTerm(definingTwoelton);
		} else {
			invariantCandidateTerm = notEqualTerm(definingTwoelton);
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

	private Twoelton<Term> constructDefiningTwoelton(Twoelton<Term> inVarTwoelton) {
		Term oneElement = inVarTwoelton.getOneElement();
		Term otherElement = inVarTwoelton.getOtherElement();
		Term[] translatedOne = RewriteArrays.translateTermVariablesToDefinitions(
				m_Script, m_VarCollector, oneElement);
		assert translatedOne.length == 1;
		Term[] translatedOther = RewriteArrays.translateTermVariablesToDefinitions(
				m_Script, m_VarCollector, otherElement);
		assert translatedOther.length == 1;
		return new Twoelton<Term>(translatedOne[0], translatedOther[0]);
		
	}

	private boolean containsTermVariable(Twoelton<Term> twoelton) {
		if (twoelton.getOneElement().getFreeVars().length > 0) {
			return true;
		} else if (twoelton.getOtherElement().getFreeVars().length > 0) {
			return true;
		} else {
			return false;
		}
	}

	private void markForComparison(Term term1, Term term2) {
		Twoelton<Term> twoElton = new Twoelton<Term>(term1, term2);
		allTwoeltons.addTowelton(twoElton);
		if (RewriteArrays.allVariablesAreInVars(term1, m_VarCollector) && RewriteArrays.allVariablesAreInVars(term2, m_VarCollector)) {
			inVarTwoeltons.addTowelton(twoElton);
		}
	}

	public SetOfTwoeltons<Term> getDistinctTwoeltons() {
		return distinctTwoeltons;
	}

	public SetOfTwoeltons<Term> getEqualTwoeltons() {
		return equalTwoeltons;
	}

	public SetOfTwoeltons<Term> getUnknownTwoeltons() {
		return unknownTwoeltons;
	}

	public Collection<Term> getSupportingInvariants() {
		return m_SupportingInvariants;
	}

	public Term getAdditionalConjunctsEqualities() {
		return Util.and(m_Script, m_AdditionalEqualities.toArray(new Term[m_AdditionalEqualities.size()]));
	}
	
	public Term getAdditionalConjunctsNotEquals() {
		return Util.and(m_Script, m_AdditionalNotequals.toArray(new Term[m_AdditionalNotequals.size()]));
	}
	
	
	
	
}
