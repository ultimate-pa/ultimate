package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.RewriteArrays;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

public class IndexAnalyzer {
	private final SetOfTwoeltons<Term> allTwoeltons = new SetOfTwoeltons<>();
	private final SetOfTwoeltons<Term> inVarTwoeltons = new SetOfTwoeltons<>();
	private final Term m_Term;
	private final Script m_Script;
	private final VarCollector m_VarCollector;
	
	private final SetOfTwoeltons<Term> distinctTwoeltons = new SetOfTwoeltons<>();
	private final SetOfTwoeltons<Term> equalTwoeltons = new SetOfTwoeltons<>();
	private final SetOfTwoeltons<Term> unknownTwoeltons = new SetOfTwoeltons<>();
	
	
	public IndexAnalyzer(Term term, HashRelation<TermVariable, List<Term>> array2Indices, Script script, VarCollector varCollector) {
		super();
		m_Term = term;
		m_Script = script;
		m_VarCollector = varCollector;
		foo(array2Indices);
	}

	void foo(HashRelation<TermVariable, List<Term>> array2Indices) { 
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
		
		for (Twoelton<Term> twoelton : inVarTwoeltons.elements()) {
			if (containsTermVariable(twoelton)) {
				
			}
			
		}
		

		m_Script.push(1);
		Map<Term, Term> substitutionMapping = SmtUtils.termVariables2Constants(m_Script, m_Term.getFreeVars());
		SafeSubstitution subst = new SafeSubstitution(m_Script, substitutionMapping);
		m_Script.assertTerm(subst.transform(m_Term));
		for (Twoelton<Term> twoelton : allTwoeltons.elements()) {
			Term equal = subst.transform(
					SmtUtils.binaryEquality(m_Script, 
							twoelton.getOneElement(), twoelton.getOtherElement()));
			m_Script.push(1);
			m_Script.assertTerm(equal);
			LBool lbool = m_Script.checkSat();
			m_Script.pop(1);
			if (lbool == LBool.UNSAT) {
				distinctTwoeltons.addTowelton(twoelton);
			} else {
				Term notEqual = Util.not(m_Script, equal);
				m_Script.push(1);
				m_Script.assertTerm(notEqual);
				lbool = m_Script.checkSat();
				m_Script.pop(1);
				if (lbool == LBool.UNSAT) {
					equalTwoeltons.addTowelton(twoelton);
				} else {
					unknownTwoeltons.addTowelton(twoelton);
				}
			}
		}
		m_Script.pop(1);
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
	
	
}
