/*
 * Copyright (C) 2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2015 University of Freiburg
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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class IncrementalInclusionCheckDifference<LETTER, STATE, SF extends IIntersectionStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
		extends InclusionViaDifference<LETTER, STATE, SF> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {
	public IncrementalInclusionCheckDifference(final AutomataLibraryServices services,
			final IIncrementalInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> a, final List<INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>> b)
			throws AutomataLibraryException {
		super(services, stateFactory, a);
		mLogger.info(startMessage());
		for (final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> bi : b) {
			addSubtrahend(bi);
		}
		// obtain counterexample, counterexample is null if inclusion holds
		mLogger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "IncrementalInclusionCheckDifference";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Exit " + operationName() + ". Result has " + size() + " states.";
	}

	@Override
	public Boolean getResult() {
		return getCounterexample() == null;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return true;
	}
}
