/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder;

import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.AutomatonState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.AutomatonTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.AutomatonTransition.Transition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultAnnotations;

/**
 * A custom variant of NwaToUltimateModel for preference monitor automata.
 *
 * <ul>
 * <li>groups multiple edges with same predecessor and successor, to keep the automaton readable</li>
 * <li>annotates states with (a linearization of) the order on the alphabet, for non-positional preference orders</li>
 * </ul>
 *
 * @param <L>
 *            the type of letters
 * @param <S>
 *            the type of monitor states
 */
public class PreferenceMonitorToUltimateModel<L, S> extends NwaToUltimateModel<L, S> {
	private final IPreferenceOrder<L, ?, S> mOrder;
	private int mStateCounter;

	public PreferenceMonitorToUltimateModel(final AutomataLibraryServices services,
			final IPreferenceOrder<L, ?, S> order) throws AutomataOperationCanceledException {
		super(services, order.getMonitor());
		mOrder = order;
	}

	@Override
	protected AutomatonState createState(final S state) {
		final var name = "s" + mStateCounter;
		mStateCounter++;
		final var autState = new AutomatonState(name, mOrder.getMonitor().isFinal(state));

		final var annot = new DefaultAnnotations();
		annot.getAnnotationsAsMap().put("Name", state.toString());

		// For positional orders, the order also depends on the program state (not given here); so skip them.
		if (!mOrder.isPositional()) {
			final var list = mOrder.getMonitor().getAlphabet().stream().sorted(mOrder.getOrder(null, state))
					.map(Object::toString).toList();
			annot.getAnnotationsAsMap().put("Order (linearized)", list);
		}

		autState.getPayload().getAnnotations().put("Preference order", annot);

		return autState;
	}

	@Override
	protected void addTransitions(final AutomatonState vsn, final Transition transitionType, final String hierPred,
			final Iterable<? extends IOutgoingTransitionlet<L, S>> transitions) {

		final var transitionsBySucc = StreamSupport.stream(transitions.spliterator(), false)
				.collect(Collectors.groupingBy(IOutgoingTransitionlet::getSucc));
		for (final var entry : transitionsBySucc.entrySet()) {
			final S succState = entry.getKey();
			final AutomatonState succVsn = getOrConstructState(succState);
			if (entry.getValue().size() == 1) {
				final var trans = entry.getValue().getFirst();
				final L symbol = trans.getLetter();
				new AutomatonTransition(vsn, transitionType, symbol, hierPred, succVsn);
			} else {
				final var transition =
						new AutomatonTransition(vsn, transitionType, entry.getValue(), hierPred, succVsn);
				final var annot = new DefaultAnnotations();
				annot.getAnnotationsAsMap().put("Symbols", entry.getValue().stream().map(Object::toString).toList());
				transition.getPayload().getAnnotations().put("Merged edge", annot);
			}
		}
	}
}
