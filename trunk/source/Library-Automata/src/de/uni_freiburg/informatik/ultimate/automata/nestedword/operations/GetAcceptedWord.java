/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;

public class GetAcceptedWord<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	
	private NestedWord<LETTER> mAcceptedWord;

	/**
	 * @param services Ultimate services
	 * @param operand operand
	 * @throws AutomataLibraryException if construction fails
	 */
	public GetAcceptedWord(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand)
					throws AutomataLibraryException {
		super(services);
		mOperand = operand;
		mLogger.info(startMessage());
		final IsEmpty<LETTER, STATE> isEmpty = new IsEmpty<LETTER, STATE>(mServices, operand);
		if (isEmpty.getResult()) {
			throw new IllegalArgumentException(
					"unable to get word from empty language");
		} else {
			mAcceptedWord = isEmpty.getNestedRun().getWord();
		}
		mLogger.info(exitMessage());
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public NestedWord<LETTER> getResult() {
		return mAcceptedWord;
	}

	@Override
	public String operationName() {
		return "getAcceptedWord";
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Found word of length "
				+ mAcceptedWord.length();
	}
}
