package de.uni_freiburg.informatik.ultimate.heapseparator;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ArrayFinder extends TermTransformer {
	TermVariable marrayId;
	
	public ArrayFinder(Term t) {
		transform(t);
	}

	@Override
	protected void convert(final Term term) {
		if (term.getSort().isArraySort() && term instanceof TermVariable) {
			marrayId = (TermVariable) term;
			setResult(term);
			return;
		}
		super.convert(term);
	}

	TermVariable getResult() {
		return marrayId;
	}
}