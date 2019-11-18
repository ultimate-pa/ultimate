package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class CoenabledRelation<LETTER> {

	private final HashRelation<LETTER, LETTER> mRelation;

	private CoenabledRelation(final HashRelation<LETTER, LETTER> relation) {
		mRelation = relation;
	}

	public static <PLACE, LETTER> CoenabledRelation<LETTER> fromPetriNet(final AutomataLibraryServices services,
			IPetriNet<LETTER, PLACE> petriNet) throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final BranchingProcess<LETTER, PLACE> bp = new FinitePrefix<>(services, petriNet).getResult();
		return new CoenabledRelation<LETTER>(computeFromBranchingProcess(bp));
	}

	private static <PLACE, LETTER> HashRelation<LETTER, LETTER> computeFromBranchingProcess(
			final BranchingProcess<LETTER, PLACE> bp) {
		final HashRelation<LETTER, LETTER> hashRelation = new HashRelation<>();
		final ICoRelation<LETTER, PLACE> coRelation = bp.getCoRelation();
		final Collection<Event<LETTER, PLACE>> events = bp.getEvents();
		for (final Event<LETTER, PLACE> event1 : events) {
			final Set<Event<LETTER, PLACE>> coRelatedEvents = coRelation.computeCoRelatatedEvents(event1);
			for (final Event<LETTER, PLACE> coRelatedEvent : coRelatedEvents) {
				hashRelation.addPair(event1.getTransition().getSymbol(), coRelatedEvent.getTransition().getSymbol());
			}
		}
		return hashRelation;
	}

	public int size() {
		return mRelation.size();
	}
	
	public Set<LETTER> getImage(LETTER element) {
		return mRelation.getImage(element);
	}

	public void copyRelationships(LETTER from, LETTER to) {
		for (LETTER t3 : mRelation.getImage(from)) {
			mRelation.addPair(to, t3);
		}
		for (LETTER t3 : mRelation.getDomain()) {
			if (mRelation.containsPair(t3, from)) {
				mRelation.addPair(t3, to);
			}
		}
	}

	public void deleteElement(LETTER letter) {
		mRelation.removeDomainElement(letter);
		mRelation.removeRangeElement(letter);
	}
}
