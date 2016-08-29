/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

public abstract class DoubleDeckerBuilder<LETTER,STATE>
		extends DoubleDeckerVisitor<LETTER,STATE>
		implements IOpWithDelayedDeadEndRemoval<LETTER, STATE> {

	Set<STATE> mSuccessorsConstructedIn = new HashSet<STATE>();
	Set<STATE> mSuccessorsConstructedCa = new HashSet<STATE>();
//	Set<STATE> mSuccessorsConstructedRe = new HashSet<STATE>();
	
	public DoubleDeckerBuilder(final AutomataLibraryServices services) {
		super(services);
	}
	
	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final STATE up = doubleDecker.getUp();
		if (mSuccessorsConstructedIn.contains(up)) {
			final HashSet<STATE> succs = new HashSet<STATE>();
			for (final LETTER letter : mTraversedNwa.lettersInternal(up)) {
				for (final OutgoingInternalTransition<LETTER, STATE> trans :
						mTraversedNwa.internalSuccessors(up, letter)) {
					succs.add(trans.getSucc());
				}
			}
			return succs;
		} else {
			mSuccessorsConstructedIn.add(up);
			return buildInternalSuccessors(doubleDecker);
		}
	}
	
	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final STATE up = doubleDecker.getUp();
		if (mSuccessorsConstructedCa.contains(up)) {
			final HashSet<STATE> succs = new HashSet<STATE>();
			for (final LETTER letter : mTraversedNwa.lettersCall(up)) {
				for (final OutgoingCallTransition<LETTER, STATE> trans :
						mTraversedNwa.callSuccessors(up, letter)) {
					succs.add(trans.getSucc());
				}
			}
			return succs;
		} else {
			mSuccessorsConstructedCa.add(up);
			return buildCallSuccessors(doubleDecker);
		}
	}



	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
//		STATE up = doubleDecker.getUp();
//		if (mSuccessorsConstructedRe.contains(up)) {
//			return mTraversedNwa.succReturn(up);
//		} else {
//			mSuccessorsConstructedRe.add(up);
			return buildReturnSuccessors(doubleDecker);
//		}
	}
	

	protected abstract Collection<STATE> buildInternalSuccessors(
			DoubleDecker<STATE> doubleDecker);

	protected abstract Collection<STATE> buildCallSuccessors(
			DoubleDecker<STATE> doubleDecker);

	protected abstract Collection<STATE> buildReturnSuccessors(
			DoubleDecker<STATE> doubleDecker);
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mTraversedNwa;
	}

}
