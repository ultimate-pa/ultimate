package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;

public final class BuchiUnfolder<L, P> extends PetriNetUnfolderInfinite<L, P> {

	public BuchiUnfolder(final AutomataLibraryServices services, final IPetriNetTransitionProvider<L, P> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	@Override
	void setupChild() {
		mLassoChecker = new BuchiWordCheck<>(mServices, mUnfolding, (IPetriNetTransitionProvider<L, P>) mOperand);
		mLassoRun = null;
	}
}
