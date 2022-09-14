package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations.RabinWordCheck;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;

public final class RabinUnfolder<L, P> extends PetriNetUnfolderInfinite<L, P> {

	public RabinUnfolder(final AutomataLibraryServices services, final IPetriNetTransitionProvider<L, P> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	@Override
	void setupChild() {

		if (mOperand instanceof BoundedPetriNet) {
			mLassoChecker = new RabinWordCheck<>(mServices, mUnfolding,
					new BoundedRabinPetriNet<>((BoundedPetriNet<L, P>) mOperand));
		} else {
			mLassoChecker = new RabinWordCheck<>(mServices, mUnfolding, (IRabinPetriNet<L, P>) mOperand);
		}
		mLassoRun = null;
	}
}