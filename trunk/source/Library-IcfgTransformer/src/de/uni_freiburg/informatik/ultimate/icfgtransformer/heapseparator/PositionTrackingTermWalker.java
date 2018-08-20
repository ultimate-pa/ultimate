package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures.SubtreePosition;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive.TermWalker;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PositionTrackingTermWalker extends TermWalker {

	protected final SubtreePosition mSubTreePosition;

	public PositionTrackingTermWalker(final Term term, final SubtreePosition position) {
		super(term);
		mSubTreePosition = position;
	}

	@Override
	public void walk(final NonRecursive walker, final ConstantTerm term) {
		// TODO Auto-generated method stub

	}

	@Override
	public void walk(final NonRecursive walker, final AnnotatedTerm term) {
		// TODO Auto-generated method stub

	}

	@Override
	public void walk(final NonRecursive walker, final ApplicationTerm term) {
		// TODO Auto-generated method stub

	}

	@Override
	public void walk(final NonRecursive walker, final LetTerm term) {
		// TODO Auto-generated method stub

	}

	@Override
	public void walk(final NonRecursive walker, final QuantifiedFormula term) {
		// TODO Auto-generated method stub

	}

	@Override
	public void walk(final NonRecursive walker, final TermVariable term) {
		// TODO Auto-generated method stub

	}

}
