/*
 * Copyright (C) 2020 heizmann@informatik.uni-freiburg.de
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Constructs a copy of an {@link IPetriNet} in which some flow and some places are removed.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 *            Type of letters in alphabet of Petri net
 * @param <PLACE>
 *            Type of places in Petri net
 */
public class ProjectToSubnet<LETTER, PLACE> {

	private final BoundedPetriNet<LETTER, PLACE> mResult;
	private final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> mInput2Projected;

	public ProjectToSubnet(final AutomataLibraryServices services, final IPetriNet<LETTER, PLACE> operand,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> flowToRemove, final Set<PLACE> placesToRemove) {
		mResult = new BoundedPetriNet<>(services, operand.getAlphabet(), false);
		mInput2Projected = new HashMap<>();
		for (final PLACE p : operand.getPlaces()) {
			if (!placesToRemove.contains(p)) {
				mResult.addPlace(p, operand.getInitialPlaces().contains(p), operand.isAccepting(p));
			}
		}
		for (final Transition<LETTER, PLACE> t : operand.getTransitions()) {
			final HashSet<PLACE> preds = new HashSet<>(t.getPredecessors());
			preds.removeAll(flowToRemove.getImage(t));
			preds.removeAll(placesToRemove);
			final HashSet<PLACE> succs = new HashSet<>(t.getSuccessors());
			succs.removeAll(flowToRemove.getImage(t));
			succs.removeAll(placesToRemove);
			final Transition<LETTER, PLACE> newTransition =
					mResult.addTransition(t.getSymbol(), ImmutableSet.of(preds), ImmutableSet.of(succs));
			mInput2Projected.put(t, newTransition);
		}
	}

	public BoundedPetriNet<LETTER, PLACE> getResult() {
		return mResult;
	}

	public Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> getTransitionMapping() {
		return mInput2Projected;
	}
}
