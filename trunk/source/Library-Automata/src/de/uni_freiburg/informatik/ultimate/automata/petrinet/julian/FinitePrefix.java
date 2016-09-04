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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.UnaryNetOperation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.PetriNetUnfolder.order;

public class FinitePrefix<LETTER,STATE> extends UnaryNetOperation<LETTER, STATE> {
	
	private final BranchingProcess<LETTER,STATE> mResult;
	
	/**
	 * Constructor.
	 * 
	 * @param services Ultimate services
	 * @param operand operand
	 * @throws AutomataLibraryException if construction fails
	 */
	public FinitePrefix(final AutomataLibraryServices services,
			final PetriNetJulian<LETTER,STATE> operand)
					throws AutomataLibraryException {
		super(services, operand);
		mLogger.info(startMessage());
		final PetriNetUnfolder<LETTER,STATE> unf =
				new PetriNetUnfolder<LETTER,STATE>(
						mServices, operand, order.ERV, true, false);
		mResult = unf.getFinitePrefix();
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "finitePrefix";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName()
			+ " Result " + mResult.sizeInformation();
	}

	@Override
	public BranchingProcess<LETTER,STATE> getResult() {
		return mResult;
	}
}
