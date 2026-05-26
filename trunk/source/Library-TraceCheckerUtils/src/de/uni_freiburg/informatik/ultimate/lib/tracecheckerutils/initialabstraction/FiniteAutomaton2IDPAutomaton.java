/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.util.ISRLabelHandler;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.util.ISRLabelHandler.IDPLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class FiniteAutomaton2IDPAutomaton<L extends IIcfgTransition<?>, S>
		implements INwaOutgoingLetterAndTransitionProvider<L, S> {

	private final ISRLabelHandler mIsrLabelHandler;
	private final Map<IcfgLocation, IcfgLocation> mPetriNetLoc2IcfgLoc;
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mFiniteAutomaton;
	private final Set<IcfgLocation> mErrorLocations;

	public FiniteAutomaton2IDPAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final ISRLabelHandler labelHandler, final Map<IcfgLocation, IcfgLocation> petriNetLoc2IcfgLoc,
			final Set<IcfgLocation> errorLocs) {
		mIsrLabelHandler = labelHandler;
		mPetriNetLoc2IcfgLoc = petriNetLoc2IcfgLoc;
		mFiniteAutomaton = operand;
		mErrorLocations = errorLocs;
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		final var petriSuccessors = mFiniteAutomaton.internalSuccessors(state, letter);
		return () -> StreamSupport.stream(petriSuccessors.spliterator(), false).filter(t -> isIdpTransition(t, state))
				.iterator();
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state) {
		final var petriSuccessors = mFiniteAutomaton.internalSuccessors(state);
		return () -> StreamSupport.stream(petriSuccessors.spliterator(), false).filter(t -> isIdpTransition(t, state))
				.iterator();
	}

	private boolean isIdpTransition(final OutgoingInternalTransition<L, S> transition, final S state) {
		final var petriSucc = mFiniteAutomaton.internalSuccessors(state);
		final var predecessors = StreamSupport.stream(petriSucc.spliterator(), false)
				.map(t -> t.getLetter().getSource()).collect(Collectors.toSet());
		final var predISRLoc = predecessors.stream()
				.map(l -> mIsrLabelHandler.getIDPLocation(mPetriNetLoc2IcfgLoc.get(l))).collect(Collectors.toSet());
		final var letter = transition.getLetter();
		final var succLoc = mPetriNetLoc2IcfgLoc.get(letter.getTarget());
		assert !predISRLoc.isEmpty() && !predISRLoc.contains(null) && succLoc != null;
		final var allMainOrExit = predISRLoc.stream().allMatch(loc -> loc.location() == IDPLocation.MAIN);
		if (allMainOrExit) {
			return true;
		}
		final var activeIsr = DataStructureUtils.getOneAndOnly(
				predISRLoc.stream().filter(i -> i.location() != IDPLocation.MAIN).toList(), "active isr");
		final var predLoc = mIsrLabelHandler.getIDPLocation(mPetriNetLoc2IcfgLoc.get(letter.getSource()));
		if (activeIsr != predLoc) {
			return false;
		}
		return true;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mFiniteAutomaton.getVpAlphabet();
	}

	@Override
	public S getEmptyStackState() {
		return mFiniteAutomaton.getEmptyStackState();
	}

	@Override
	public Iterable<S> getInitialStates() {
		return mFiniteAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(final S state) {
		return mFiniteAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return mFiniteAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		return mFiniteAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return mFiniteAutomaton.sizeInformation();
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		return Collections.emptySet();
	}
}
