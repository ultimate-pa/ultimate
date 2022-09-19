package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
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
	private final PetriNetLassoRun<LETTER, PLACE> mRun;

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
		final BuchiUnfolder<LETTER, PLACE> unf =
				new BuchiUnfolder<>(mServices, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
		mRun = unf.getAcceptingRun();
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
		return mRun == null;
	}

	@Override
	public boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> finiteAutomaton =
				(new BuchiPetriNet2FiniteAutomaton<>(mServices, stateFactory,
						(IBlackWhiteStateFactory<PLACE>) stateFactory, mOperand)).getResult();
		final boolean automatonEmpty =
				(new de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIsEmpty<>(mServices,
						finiteAutomaton)).getResult();
		return getResult() == automatonEmpty;
	}
}
