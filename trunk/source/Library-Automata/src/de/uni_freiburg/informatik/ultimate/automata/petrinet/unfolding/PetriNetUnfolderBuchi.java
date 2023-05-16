package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.PetriNetUnfolder.EventOrderEnum;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

public class PetriNetUnfolderBuchi<LETTER, PLACE>
		extends PetriNetUnfolderBase<LETTER, PLACE, PetriNetLassoRun<LETTER, PLACE>> {
	public PetriNetUnfolderBuchi(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	@Override
	protected boolean checkInitialPlacesAndCreateRun() {
		return false;
	}

	@Override
	protected boolean addAndCheck(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {

		mUnfolding.addEvent(event);

		// Investigating if local configuration contains lasso word
		if (event.isCutoffEvent() && event.getLocalConfiguration().contains(event.getCompanion())) {

			final List<Event<LETTER, PLACE>> configLoopEvents = new ArrayList<>();
			final List<Event<LETTER, PLACE>> configStemEvents = new ArrayList<>();
			for (final Event<LETTER, PLACE> configEvent : event.getLocalConfiguration()
					.getSortedConfiguration(mUnfolding.getOrder())) {
				if (configEvent != event.getCompanion()
						&& configEvent.getLocalConfiguration().contains(event.getCompanion())) {
					configLoopEvents.add(configEvent);
				} else {
					configStemEvents.add(configEvent);
				}
			}
			return checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents);
		}
		return false;
	}

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		final var buildAndCheck =
				new Events2PetriNetLassoRunBuchi<>(mServices, configLoopPart, configStemPart, mUnfolding);
		mRun = buildAndCheck.getLassoRun();
		return mRun != null;
	}

	@Override
	protected void updateRunIfWanted(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		// Nothing to do, the run was already created in checkIfLassoConfigurationAccepted
	}

	@Override
	protected void createRunFromWholeUnfolding() throws PetriNetNot1SafeException {
		mRun = new CanonicalPrefixIsEmptyBuchi<>(mServices, mUnfolding).getLassoRun();
	}

	@Override
	boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		// Not implemented yet
		return true;
	}
}
