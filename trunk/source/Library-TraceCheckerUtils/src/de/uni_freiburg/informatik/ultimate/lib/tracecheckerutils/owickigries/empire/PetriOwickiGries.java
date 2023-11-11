package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class PetriOwickiGries<LETTER, PLACE> {

	private final BranchingProcess<LETTER, PLACE> mBp;
	private final Set<Condition<LETTER, PLACE>> mConditions;
	private final Set<Condition<LETTER, PLACE>> mOriginalConditions;
	private final Set<Condition<LETTER, PLACE>> mAssertionConditions;
	private final Set<PLACE> mOriginalPlaces;
	private final IPetriNet<LETTER, PLACE> mNet;
	private final Crown<PLACE, LETTER> mCrown;

	public PetriOwickiGries(final BranchingProcess<LETTER, PLACE> bp, final IPetriNet<LETTER, PLACE> net) {
		mBp = bp;
		mNet = net;
		mOriginalPlaces = mNet.getPlaces();
		mConditions = mBp.getConditions().stream().collect(Collectors.toSet());
		mOriginalConditions = getOrigConditions();
		mAssertionConditions = DataStructureUtils.difference(mConditions, mOriginalConditions);
		mCrown = getCrown();
	}

	private Crown<PLACE, LETTER> getCrown() {
		CrownConstruction<PLACE, LETTER> crownConstruction =
				new CrownConstruction<>(mBp, mOriginalConditions, mAssertionConditions);
		return crownConstruction.getCrown();
	}

	private Set<Condition<LETTER, PLACE>> getOrigConditions() {
		final Set<Condition<LETTER, PLACE>> conditions = new HashSet<>();
		for (final Condition<LETTER, PLACE> cond : mBp.getConditions()) {
			if (mOriginalPlaces.contains(cond.getPlace())) {
				conditions.add(cond);
			}
		}
		return conditions;
	}
}
