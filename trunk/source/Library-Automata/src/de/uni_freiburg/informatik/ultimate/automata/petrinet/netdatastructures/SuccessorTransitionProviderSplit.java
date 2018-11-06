/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;

/**
 * Split {@link ISuccessorTransitionProvider} in two
 * {@link ISuccessorTransitionProvider}s. One provides all transitions such that
 * the letter is in a given set, the other provides all transitions that are not
 * in the set.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class SuccessorTransitionProviderSplit<LETTER, PLACE> {

	private final ISuccessorTransitionProvider<LETTER, PLACE> mSuccTransProviderLetterInSet;
	private final ISuccessorTransitionProvider<LETTER, PLACE> mSuccTransProviderLetterNotInSet;

	public SuccessorTransitionProviderSplit(final ISuccessorTransitionProvider<LETTER, PLACE> succTransProvider,
			final Set<LETTER> letterSet, final IPetriNetSuccessorProvider<LETTER, PLACE> net) {
		super();
		final List<ITransition<LETTER, PLACE>> transWithLetterInSet = new ArrayList<>();
		final List<ITransition<LETTER, PLACE>> transWithLetterNotInSet = new ArrayList<>();
		for (final ITransition<LETTER, PLACE> trans : succTransProvider.getTransitions()) {
			if (letterSet.contains(trans.getSymbol())) {
				transWithLetterInSet.add(trans);
			} else {
				transWithLetterNotInSet.add(trans);
			}
		}
		if (transWithLetterInSet.isEmpty()) {
			mSuccTransProviderLetterInSet = null;
		} else {
			mSuccTransProviderLetterInSet = new SimpleSuccessorTransitionProvider<>(transWithLetterInSet, net);
		}
		if (transWithLetterNotInSet.isEmpty()) {
			mSuccTransProviderLetterNotInSet = null;
		} else {
			mSuccTransProviderLetterNotInSet = new SimpleSuccessorTransitionProvider<>(transWithLetterNotInSet, net);
		}
	}

	public ISuccessorTransitionProvider<LETTER, PLACE> getSuccTransProviderLetterInSet() {
		return mSuccTransProviderLetterInSet;
	}

	public ISuccessorTransitionProvider<LETTER, PLACE> getSuccTransProviderLetterNotInSet() {
		return mSuccTransProviderLetterNotInSet;
	}



}
