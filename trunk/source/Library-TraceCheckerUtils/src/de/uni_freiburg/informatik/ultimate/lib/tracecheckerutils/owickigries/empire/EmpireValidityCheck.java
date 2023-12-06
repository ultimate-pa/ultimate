package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Check a given Empire annotation for validity i.e. the initial markings law evaluates to true and every accepting
 * markings law evaluates to false. Further for all other markings m1, m2 must hold: If there is a firing relation f_t
 * between m1 and m2 then the Hoare-Triple {m1}t{m2} is valid.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public class EmpireValidityCheck<PLACE, LETTER> {
	private final MarkingLaw<PLACE, LETTER> mMarkingLaw;
	private final BasicPredicateFactory mFactory;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final MonolithicImplicationChecker mImplicationChecker;
	private final Validity mValidity;

	public EmpireValidityCheck(final MarkingLaw<PLACE, LETTER> markingLaw, final IPetriNet<LETTER, PLACE> net,
			final BasicPredicateFactory factory, final MonolithicImplicationChecker implicationChecker) {
		mMarkingLaw = markingLaw;
		mFactory = factory;
		mNet = net;
		mImplicationChecker = implicationChecker;
		mValidity = checkValidity();
		assert mValidity == Validity.VALID : "Empire annotation is not valid";
	}

	private boolean checkInitialMarking() {
		final Marking<PLACE> initialMarking = new Marking<>(ImmutableSet.copyOf(mNet.getInitialPlaces()));
		final IPredicate trueIPredicate = mFactory.and();
		return mImplicationChecker.checkImplication(trueIPredicate, false, mMarkingLaw.getMarkingLaw(initialMarking),
				false) == Validity.VALID;
	}

	private boolean checkFinalMarkings() {
		final Set<PLACE> acceptingPlaces = mNet.getAcceptingPlaces();
		for (final Marking<PLACE> marking : mMarkingLaw.getMarkings()) {
			if (marking.containsAny(acceptingPlaces)) {
				return false;
			}
		}
		return true;
	}

	public Validity checkValidity() {
		final boolean initialMarkingValidity = checkInitialMarking();
		assert initialMarkingValidity : "Initial markings law does not evaluate to true.";
		final boolean finalMarkingValidity = checkFinalMarkings();
		assert finalMarkingValidity : "Final markings law does not evaluate to false";
		if (!initialMarkingValidity || !finalMarkingValidity) {
			return Validity.INVALID;
		}
		return Validity.VALID;
	}

	public Validity getValidity() {
		return mValidity;
	}
}
