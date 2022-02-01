/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNwaTv;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Test class to produce benchmark results.
 * <p>
 * Constructs random nested word automata.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class ConstructRandomAutomata implements IOperation<String, String, IStateFactory<String>> {
	private static final int NUMBER_OF_SAMPLES = 100;
	private static final String AUTOMATON_NAME_PREFIX = "Random";

	public ConstructRandomAutomata(final AutomataLibraryServices services) {
		for (int i = 0; i < NUMBER_OF_SAMPLES; ++i) {
			final INestedWordAutomaton<String, String> random =
					new GetRandomNwaTv(services, 50, 2, 2, 2, 100, 100, 100, 50, 50).getResult();
			INestedWordAutomaton<String, String> nwa;
			try {
				nwa = new RemoveDeadEnds(services, random).getResult();
			} catch (final AutomataOperationCanceledException e) {
				e.printStackTrace();
				continue;
			}
			final String fileName = AUTOMATON_NAME_PREFIX + i;
			AutomatonDefinitionPrinter.writeToFileIfPreferred(services, fileName, "random automaton dump", nwa);
		}
	}

	@Override
	public String startMessage() {
		return null;
	}

	@Override
	public String exitMessage() {
		return null;
	}

	@Override
	public Object getResult() {
		return null;
	}

	@Override
	public boolean checkResult(final IStateFactory<String> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
