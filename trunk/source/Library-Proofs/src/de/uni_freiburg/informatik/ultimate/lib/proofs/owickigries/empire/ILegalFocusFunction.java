/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;

/**
 * Abstract interface for legal focus.
 *
 * A legal focus assigns potentially different laws to different regions in the territory belonging to an empire. For
 * each region, the assigned law must be weaker than the state's full law, and satisfy additional conditions:
 *
 * <ol>
 * <li><em>safe</em>: if a transition is enabled in a state's territory, but the state has no outgoing edge for this
 * transition (i.e., it must lead to "false"), then some predecessor region of the transition must be in the focus of
 * some conjunct that suffices to derive "false" after the transition.</li>
 *
 * <li><em>inductive-edge</em>: if the focus successor region of a transition in some state contains the i-th law
 * conjunct of the state, then the focus of some predecessor region of the transition must, in the predecessor state,
 * contain the respective i-th law conjunct.</li>
 *
 * <li><em>bystanders</em>: executing a transition does not increase the focus of the transition's bystanders.</li>
 * </ol>
 *
 * The formal definitions can be found in our POPL'26 paper, Section 6.
 *
 * @param <S>
 *            the type of states in the empire
 * @param <P>
 *            the type of places in the regions
 */
public interface ILegalFocusFunction<S, P> {
	/**
	 * Returns the focused law for the given state and region.
	 *
	 * For technical reasons, we currently allow returning a list, which is treated as a conjunction.
	 *
	 * @param state
	 * @param region
	 * @return
	 */
	List<IPredicate> getFocusedLaws(S state, Region<P> region);

	/**
	 * Implements the trivial focus function, which assigns the full law of the state to every region.
	 *
	 * @param <S>
	 *            the type of states in the empire
	 * @param <P>
	 *            the type of places in the regions
	 */
	class TrivialFocus<S, P> implements ILegalFocusFunction<S, P> {
		private final IEmpire<?, P, S> mEmpire;

		public TrivialFocus(final IEmpire<?, P, S> empire) {
			mEmpire = empire;
		}

		@Override
		public List<IPredicate> getFocusedLaws(final S state, final Region<P> region) {
			assert mEmpire.getTerritory(state).getRegions().contains(region)
					: "Region " + region + " does not occur in territory of state " + state;
			return PredicateWithConjuncts.flatten(mEmpire.getLaw(state));
		}
	}
}
