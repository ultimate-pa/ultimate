/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ComplementDeterministicNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.DeterminizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;

/**
 * This is an implementation of our incremental inclusion check based on a difference construction. This implementation
 * is not efficient and should not used in practice. We use this implementation only for comparison with the "real"
 * incremental inclusion. This implementation could be improved by applying a removal of dead ends and a minimization to
 * the difference after each step.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class InclusionViaDifference<LETTER, STATE, SF extends IIntersectionStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
		extends AbstractIncrementalInclusionCheck<LETTER, STATE> {
	private final SF mStateFactoryIntersect;
	private final IDeterminizeStateFactory<STATE> mStateFactoryDeterminize;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mDifference;
	private NestedRun<LETTER, STATE> mAcceptingRun;

	private final boolean mRemoveDeadEnds = true;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param nwaA
	 *            minuend
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	@SuppressWarnings("unchecked")
	public InclusionViaDifference(final AutomataLibraryServices services,
			final IIncrementalInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwaA) throws AutomataOperationCanceledException {
		this(services, (SF) stateFactory, stateFactory, nwaA);
	}

	/**
	 * Constructor that uses different stateFactories for intersection and determinization. This is currently needed
	 * when we use the inclusion check in program verification.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactoryIntersect
	 *            state factory for intersection
	 * @param stateFactoryDeterminize
	 *            state factory for determinization
	 * @param nwaA
	 *            minuend
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public InclusionViaDifference(final AutomataLibraryServices services, final SF stateFactoryIntersect,
			final IDeterminizeStateFactory<STATE> stateFactoryDeterminize,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwaA) throws AutomataOperationCanceledException {
		super(services, nwaA);
		mStateFactoryIntersect = stateFactoryIntersect;
		mStateFactoryDeterminize = stateFactoryDeterminize;
		// initialize difference. B_1,...,B_n is empty
		mDifference = nwaA;
		mAcceptingRun = (new IsEmpty<>(mServices, mDifference)).getNestedRun();
	}

	@Override
	public NestedRun<LETTER, STATE> getCounterexample() {
		return mAcceptingRun;
	}

	@Override
	public void addSubtrahend(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) throws AutomataLibraryException {
		super.addSubtrahend(nwa);
		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> determinized = new DeterminizeNwa<>(mServices, nwa,
				new PowersetDeterminizer<>(nwa, true, mStateFactoryDeterminize), mStateFactoryDeterminize, null, true);
		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> complemented = new ComplementDeterministicNwa<>(determinized);
		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> difference =
				new IntersectNwa<>(mDifference, complemented, mStateFactoryIntersect, false);
		if (mRemoveDeadEnds) {
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> removedDeadEnds =
					(new RemoveDeadEnds<>(mServices, difference)).getResult();
			mDifference = removedDeadEnds;
		} else {
			mDifference = difference;
		}
		mAcceptingRun = (new IsEmpty<>(mServices, mDifference)).getNestedRun();
	}

	/**
	 * @return The number of states in the difference.
	 */
	public int size() {
		return mDifference.size();
	}
}
