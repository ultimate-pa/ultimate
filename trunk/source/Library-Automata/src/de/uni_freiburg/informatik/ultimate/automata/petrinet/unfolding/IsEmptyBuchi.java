package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoWord;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiPetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Emptiness check for Buchi Petri nets.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            place content type
 */
public final class IsEmptyBuchi<LETTER, PLACE>
		extends UnaryNetOperation<LETTER, PLACE, IPetriNet2FiniteAutomatonStateFactory<PLACE>> {
	private final IPetriNetTransitionProvider<LETTER, PLACE> mOperand;
	private PetriNetLassoRun<LETTER, PLACE> mRun;
	private final boolean mResult;

	public IsEmptyBuchi(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());
		final PetriNetUnfolderBuchi<LETTER, PLACE> unfolder =
				new PetriNetUnfolderBuchi<>(mServices, operand, PetriNetUnfolder.EventOrderEnum.ERV, false, true);
		mRun = unfolder.getAcceptingRun();
		if (mRun == null) {
			final CanonicalPrefixIsEmptyBuchi<LETTER, PLACE> checkBuchi =
					new CanonicalPrefixIsEmptyBuchi<>(services, unfolder.getFinitePrefix());
			mRun = checkBuchi.getLassoRun();
		}
		mResult = mRun == null;
		mLogger.info(exitMessage());
	}

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 * @throws PetriNetNot1SafeException
	 */
	public IsEmptyBuchi(final AutomataLibraryServices services,
			final IPetriNetTransitionProvider<LETTER, PLACE> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());
		final PetriNetUnfolderBuchi<LETTER, PLACE> unfolder =
				new PetriNetUnfolderBuchi<>(mServices, operand, order, sameTransitionCutOff, true);
		mRun = unfolder.getAcceptingRun();
		if (mRun == null) {
			final CanonicalPrefixIsEmptyBuchi<LETTER, PLACE> checkBuchi =
					new CanonicalPrefixIsEmptyBuchi<>(services, unfolder.getFinitePrefix());
			mRun = checkBuchi.getLassoRun();
		}
		mResult = mRun == null;
		mLogger.info(exitMessage());
	}

	public PetriNetLassoRun<LETTER, PLACE> getRun() {
		return mRun;
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " language is " + (getResult() ? "empty" : "not empty");
	}

	@Override
	protected IPetriNetTransitionProvider<LETTER, PLACE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> finiteAutomaton =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mOperand, null)).getResult();
		final var emptyCheck =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty<>(mServices,
						finiteAutomaton));
		final boolean automatonEmpty = emptyCheck.getResult();
		// final var run2 = emptyCheck.getAcceptingNestedLassoRun();
		// if (getRun() != null) {
		// mLogger.info("stem mine: " + getRun().getStem());
		// mLogger.info("loop mine: " + getRun().getLoop());
		// }
		// if (run2 != null) {
		// mLogger.info("stem theirs: " + run2.getStem());
		// mLogger.info("loop theirs: " + run2.getLoop());
		// }

		boolean isAcceptedWord = true;
		if (getRun() != null) {
			final NestedWord<LETTER> nestedstemWord = NestedWord.nestedWord(getRun().getStem().getWord());
			final NestedWord<LETTER> nestedloopWord = NestedWord.nestedWord(getRun().getLoop().getWord());
			final NestedLassoWord<LETTER> nestedLassoWord = new NestedLassoWord<>(nestedstemWord, nestedloopWord);
			final var accepts = new BuchiAccepts<>(mServices, finiteAutomaton, nestedLassoWord);
			isAcceptedWord = accepts.getResult();
		}
		return getResult() == automatonEmpty && isAcceptedWord;
	}
}
