package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IRabinPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.Rpn2ra;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.rabin.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Emptiness check for Rabin Petri nets.
 *
 * @param <LETTER>
 *            letter type
 * @param <PLACE>
 *            place content type
 */
public final class RabinIsEmpty<LETTER, PLACE, FACTORY extends IBlackWhiteStateFactory<PLACE> & IPetriNet2FiniteAutomatonStateFactory<PLACE>>
		extends UnaryNetOperation<LETTER, PLACE, FACTORY> {
	private final IRabinPetriNet<LETTER, PLACE> mOperand;
	private final PetriNetLassoRun<LETTER, PLACE> mRun;

	/**
	 * A operation that determines if a {@link IRabinPetriNet} is empty
	 *
	 * @param services
	 *            services
	 * @param operand
	 *            the Rabin-Petri-Net that should be checked for emptiness
	 * @throws AutomataOperationCanceledException
	 *             a exception that can be thrown if the operation is cancelled from the outside
	 * @throws PetriNetNot1SafeException
	 *             a exception that occurs if 2 markings could be put into 1 place
	 */
	public RabinIsEmpty(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> operand)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		this(services, operand, EventOrderEnum.ERV, false, true);
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
	public RabinIsEmpty(final AutomataLibraryServices services, final IRabinPetriNet<LETTER, PLACE> operand,
			final EventOrderEnum order, final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());

		final PetriNetUnfolderRabin<LETTER, PLACE> unfolder =
				new PetriNetUnfolderRabin<>(mServices, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
		mRun = unfolder.getAcceptingRun();
		mLogger.info(exitMessage());
	}

	public PetriNetLassoRun<LETTER, PLACE> getRun() {
		return mRun;
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " language is "
				+ (Boolean.TRUE.equals(getResult()) ? "empty" : "not empty");
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
	public boolean checkResult(final FACTORY stateFactory) throws AutomataLibraryException {
		return getResult() == new IsEmpty<>(mServices, new Rpn2ra<>(mServices, stateFactory, mOperand).getResult())
				.getResult();
	}
}
