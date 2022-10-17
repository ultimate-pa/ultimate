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

public class PetriNetUnfolderBuchi<LETTER, PLACE> extends PetriNetUnfolderBase<LETTER, PLACE> {
	PetriNetLassoRun<LETTER, PLACE> mLassoRun;

	public PetriNetUnfolderBuchi(final AutomataLibraryServices services,
			final IPetriNetSuccessorProvider<LETTER, PLACE> operand, final EventOrderEnum order,
			final boolean sameTransitionCutOff, final boolean stopIfAcceptingRunFound)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		super(services, operand, order, sameTransitionCutOff, stopIfAcceptingRunFound);
	}

	public PetriNetLassoRun<LETTER, PLACE> getAcceptingRun() {
		return mLassoRun;
	}

	@Override
	protected void createInitialRun() throws PetriNetNot1SafeException {
		return;
	}

	@Override
	protected boolean checkInitialPlaces() {
		return false;
	}

	@Override
	boolean unfoldingSearchSuccessful(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {

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
			if (checkIfLassoConfigurationAccepted(configLoopEvents, configStemEvents)) {
				return true;
			}
		}
		return false;
	}

	private final boolean checkIfLassoConfigurationAccepted(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart) throws PetriNetNot1SafeException {
		final var buildAndCheck = new Events2PetriNetLassoRunBuchi<>(mServices, configLoopPart, configStemPart, mUnfolding);
		mLassoRun = buildAndCheck.getLassoRun();
		return (mLassoRun != null);
	}

	@Override
	void createOrUpdateRunIfWanted(final Event<LETTER, PLACE> event) throws PetriNetNot1SafeException {
		return;
	}

	@Override
	boolean checkResult(final IPetriNet2FiniteAutomatonStateFactory<PLACE> stateFactory)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		return true;
	}

}
