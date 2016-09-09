/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Provides static methods that are helpful for working with nested word automata 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class NestedWordAutomataUtils {
	
	public static <LETTER, STATE> void applyToReachableSuccessors(
			final IDoubleDeckerAutomaton<LETTER, STATE> mOperand, final STATE state, final Consumer<STATE> f) {
		for (final OutgoingInternalTransition<LETTER, STATE> t : mOperand.internalSuccessors(state)) {
			f.accept(t.getSucc());
		}
		for (final OutgoingCallTransition<LETTER, STATE> t : mOperand.callSuccessors(state)) {
			f.accept(t.getSucc());
		}
		for (final OutgoingReturnTransition<LETTER, STATE> t : mOperand.returnSuccessors(state)) {
			if (mOperand.isDoubleDecker(state, t.getHierPred())) {
				f.accept(t.getSucc());
			}
		}
	}

}
