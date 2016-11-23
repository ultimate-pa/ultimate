package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Runs through a Term and collects all subterms (or something more specific?) that are equated 
 * to a Term in the list of candidate Terms.
 * 
 * Currently subterms can be anything that can be a BoogieVarOrConst.
 * 
 * @author Alexander Nutz
 *
 */
public class EquatedTermsFinder extends TermTransformer {
	
	private final Set<Term> mCandidateTerms;
	
	private final Set<Term> mEquatedTerms;

	public EquatedTermsFinder(Set<Term> candidateTerms) {
		mCandidateTerms = candidateTerms;
		mEquatedTerms = new HashSet<>();
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		String funcName = appTerm.getFunction().getName();
		if ("=".equals(funcName) || "distinct".equals(funcName)) {
			if (mCandidateTerms.contains(appTerm.getParameters()[0])) {
				collect(appTerm.getParameters()[1]);
			}
			if (mCandidateTerms.contains(appTerm.getParameters()[1])) {
				collect(appTerm.getParameters()[0]);
			}
		}
		super.convertApplicationTerm(appTerm, newArgs);
	}
	
	private void collect(Term t) {
		if (t instanceof TermVariable 
				|| t instanceof ConstantTerm
				|| (t instanceof ApplicationTerm 
						&& ((ApplicationTerm) t).getParameters().length == 0)) {
			mEquatedTerms.add(t);
		}
	}
	
	public Set<Term> getEquatedTerms() {
		return mEquatedTerms;
	}

}
