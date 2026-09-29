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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Explores the reachable states of an {@link IEmpire}.
 *
 * @param <L>
 *            the type of letters in the Petri program
 * @param <P>
 *            the type of places in the Petri program
 * @param <S>
 *            the type of states in the empire
 */
public class EmpireReachableStates<L, P, S> implements IExplicitEmpire<L, P, S> {
	private final IEmpire<L, P, S> mEmpire;
	private final NestedWordAutomatonReachableStates<Transition<L, P>, S> mReachable;

	/**
	 * Creates a new instance of the class, which iteratively explores the states of the given empire.
	 *
	 * If the given empire might already be explicit, consider using the static
	 * {@link #makeExplicit(IUltimateServiceProvider, IEmpire)} method instead.
	 */
	public EmpireReachableStates(final IUltimateServiceProvider services, final IEmpire<L, P, S> empire) {
		mEmpire = empire;
		try {
			mReachable = new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(services), empire);
		} catch (final AutomataOperationCanceledException e) {
			throw new ToolchainCanceledException(e,
					new RunningTaskInfo(getClass(), "collecting reachable states of empire"));
		}
	}

	/**
	 * Turns a given empire into an explicit empire. If the given empire is already explicit, it is returned unchanged
	 * (avoiding unnecessary effort). Otherwise, a new instance of this class is created and returned.
	 */
	public static <L, P, S> IExplicitEmpire<L, P, S> makeExplicit(final IUltimateServiceProvider services,
			final IEmpire<L, P, S> empire) {
		if (empire instanceof final IExplicitEmpire<L, P, S> explicitEmpire) {
			return explicitEmpire;
		}
		return new EmpireReachableStates<>(services, empire);
	}

	@Override
	public IPredicate getLaw(final S state) {
		return mEmpire.getLaw(state);
	}

	@Override
	public Territory<P, Region<P>> getTerritory(final S state) {
		return mEmpire.getTerritory(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<Transition<L, P>, S>> internalSuccessors(final S state,
			final Transition<L, P> letter) {
		return mReachable.internalSuccessors(state, letter);
	}

	@Override
	public VpAlphabet<Transition<L, P>> getVpAlphabet() {
		return mReachable.getVpAlphabet();
	}

	@Override
	public boolean isInitial(final S state) {
		return mReachable.isInitial(state);
	}

	@Override
	public int size() {
		return mReachable.size();
	}

	@Override
	public String sizeInformation() {
		return mReachable.sizeInformation();
	}

	@Override
	public Set<S> getStates() {
		return mReachable.getStates();
	}

	@Override
	public Set<S> getInitialStates() {
		return mReachable.getInitialStates();
	}

	@Override
	public Set<Transition<L, P>> lettersInternalIncoming(final S state) {
		return mReachable.lettersInternalIncoming(state);
	}

	@Override
	public Iterable<IncomingInternalTransition<Transition<L, P>, S>> internalPredecessors(final S succ,
			final Transition<L, P> letter) {
		return mReachable.internalPredecessors(succ, letter);
	}

	@Override
	public Iterable<IncomingInternalTransition<Transition<L, P>, S>> internalPredecessors(final S succ) {
		return mReachable.internalPredecessors(succ);
	}
}
