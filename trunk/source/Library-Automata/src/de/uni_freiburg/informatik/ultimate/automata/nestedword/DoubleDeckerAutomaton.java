/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DoubleDeckerVisitor.ReachFinal;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * Basic implementation of the {@link IDoubleDeckerAutomaton} interface based on the {@link NestedWordAutomaton}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DoubleDeckerAutomaton<LETTER, STATE> extends NestedWordAutomaton<LETTER, STATE>
		implements IDoubleDeckerAutomaton<LETTER, STATE> {
	private static final String UP2DOWN_NOT_SET = "up2down not set";

	private Map<STATE, Map<STATE, ReachFinal>> mUp2Down;

	/**
	 * Constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param internalAlphabet
	 *            internal alphabet
	 * @param callAlphabet
	 *            call alphabet
	 * @param returnAlphabet
	 *            return alphabet
	 * @param stateFactory
	 *            state factory
	 */
	public DoubleDeckerAutomaton(final AutomataLibraryServices services, final VpAlphabet<LETTER> vpAlphabet,
			final IEmptyStackStateFactory<STATE> stateFactory) {
		super(services, vpAlphabet, stateFactory);
		mUp2Down = null;
	}

	/**
	 * @return true iff down state map is set.
	 */
	public boolean up2DownIsSet() {
		return mUp2Down != null;
	}

	@Override
	public Set<STATE> getDownStates(final STATE upState) {
		if (up2DownIsSet()) {
			return mUp2Down.get(upState).keySet();
		}
		throw new AssertionError(UP2DOWN_NOT_SET);
	}

	/**
	 * @param up2Down
	 *            New map (up state -> down state).
	 */
	public void setUp2Down(final Map<STATE, Map<STATE, ReachFinal>> up2Down) {
		if (up2DownIsSet()) {
			throw new AssertionError("up2down already set");
		}
		mUp2Down = up2Down;
	}

	@Override
	public boolean isDoubleDecker(final STATE upState, final STATE downState) {
		if (!up2DownIsSet()) {
			throw new AssertionError(UP2DOWN_NOT_SET);
		}
		/**
		 * TODO Christian 2016-08-21: Should the "getStates().contains()" tests be made assertions for efficiency
		 * reasons? In particular, this can be expensive for on-the-fly constructions.
		 */
		if (getStates().contains(upState)) {
			final Map<STATE, ReachFinal> downStates = mUp2Down.get(upState);
			if (getStates().contains(downState)) {
				return downStates.get(downState) != null;
			}
			return false;
		}
		return false;
	}
}
