package de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers;


import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class StripAnnotationsTermTransformer extends TermTransformer{

	protected void convert(Term term) {
		if (term instanceof AnnotatedTerm) {
			AnnotatedTerm at = (AnnotatedTerm) term;
			super.setResult(at.getSubterm());
		} else
			super.convert(term);
	}
}
