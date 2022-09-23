package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Abstract class for unfolding and checking Petri nets on infinite words for emptiness.
 *
 * @param <L>
 *            letter type
 * @param <P>
 *            place content type
 */
public abstract class PetriNetUnfolderInfinite<L, P> extends PetriNetUnfolderBase<L, P> {
	protected UnfoldingInfiniteWordCheck<L, P> mLassoChecker;

	protected PetriNetLassoRun<L, P> mLassoRun;

	/**
	 * Build the finite Prefix of PetriNet net on infinite words.
	 *
	 * @param order
	 *            the order on events and configurations respectively is used to determine cut-off events.
	 * @param sameTransitionCutOff
	 *            if true, an additional condition for cut-off events is used: An event and its companion must belong to
	 *            the same transition from the net.
	 * @param stopIfAcceptingRunFound
	 *            if false, the complete finite Prefix will be build.
	 * @throws AutomataOperationCanceledException
	 *             if timeout exceeds
	 * @throws PetriNetNot1SafeException
	 */
	public PetriNetUnfolderInfinite(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<L, P> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	@Override
	abstract void setupChild();

	public PetriNetLassoRun<L, P> getAcceptingRun() {
		return mLassoRun;
	}

	/**
	 * cannot find a loop in initial marking
	 */
	@Override
	protected boolean checkInitialPlaces() {
		return false;
	}

	@Override
	protected void createInitialRun() throws PetriNetNot1SafeException {
		return;
	}

	@Override
	boolean unfoldingSearchSuccessful(final Event<L, P> event) throws PetriNetNot1SafeException {
		mUnfolding.addEvent(event);

		boolean lassoFound = false;
		lassoFound = mLassoChecker.update(event);
		return lassoFound;
	}

	@Override
	void createOrUpdateRunIfWanted(final Event<L, P> event) throws PetriNetNot1SafeException {
		if (mLassoRun == null) {
			mLassoRun = mLassoChecker.mRun;
		}
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<P> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		return false;
	}
}
