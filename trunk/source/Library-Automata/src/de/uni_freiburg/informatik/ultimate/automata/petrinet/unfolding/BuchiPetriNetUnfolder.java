package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.buchipetrinet.operations.BuchiPetriNetEmptinessCheckWithAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public final class BuchiPetriNetUnfolder<L, P> extends PetriNetUnfolderBase<L, P> {
	private BuchiPetriNetEmptinessCheckWithAccepts<L, P> mLassoChecker;

	private PetriNetLassoRun<L, P> mLassoRun;

	/**
	 * Build the finite Prefix of PetriNet net.
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
	public BuchiPetriNetUnfolder(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<L, P> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound, final int checker)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
		mLassoChecker = null;

	}

	@Override
	void setupChild() {
		mLassoChecker = new BuchiPetriNetEmptinessCheckWithAccepts<>(mServices, mUnfolding,
				(IPetriNetTransitionProvider<L, P>) mOperand);
		mLassoRun = null;
	}

	public PetriNetLassoRun<L, P> getAcceptingRun() {
		return mLassoRun;
	}

	/*
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
			mLassoRun = constructRun();
		}
	}

	/**
	 * constructs a run over the unfolding which leads to the marking corresponding with the local configuration of the
	 * specified event e.
	 *
	 * @throws PetriNetNot1SafeException
	 */
	private PetriNetLassoRun<L, P> constructRun() throws PetriNetNot1SafeException {
		final List<Marking<P>> sequenceOfStemMarkings = new ArrayList<>();
		final List<Marking<P>> sequenceOfLassoMarkings = new ArrayList<>();
		final Pair<NestedLassoWord<L>, List<Event<L, P>>> resutlPair =
				mLassoChecker.getLassoConfigurations().iterator().next();
		final int stemlength = resutlPair.getFirst().getStem().length();
		Marking<P> currentMarking = new Marking<>(ImmutableSet.of(mOperand.getInitialPlaces()));
		sequenceOfStemMarkings.add(currentMarking);

		int wordIndex = 0;
		for (final Event<L, P> event : resutlPair.getSecond()) {
			currentMarking = currentMarking.fireTransition(event.getTransition());
			if (wordIndex < stemlength - 1) {
				sequenceOfStemMarkings.add(currentMarking);
				// TODO: Does the Petrinetrun for the lasso part have 1 marking too much ?
				// maybe don't use Petrinetrun for loop part.
			} else if (wordIndex == stemlength - 1) {
				sequenceOfStemMarkings.add(currentMarking);
				sequenceOfLassoMarkings.add(currentMarking);
			} else {
				sequenceOfLassoMarkings.add(currentMarking);
			}

			wordIndex++;
		}

		final PetriNetRun<L, P> stemRun = new PetriNetRun<>(sequenceOfStemMarkings, resutlPair.getFirst().getStem());
		final PetriNetRun<L, P> loopRun = new PetriNetRun<>(sequenceOfLassoMarkings, resutlPair.getFirst().getLoop());
		final PetriNetLassoRun<L, P> lassoRun = new PetriNetLassoRun<>(stemRun, loopRun);
		return lassoRun;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<P> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		// TODO:
		return false;
	}
}
