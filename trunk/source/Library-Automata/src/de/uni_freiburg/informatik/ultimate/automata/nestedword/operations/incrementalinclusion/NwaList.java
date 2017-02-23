/*
 * Copyright (C) 2014-2015 Jeffery Hsu (a71128@gmail.com)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Utility class that provides an interface for constructing a list of INestedWordAutomatons.
 * 
 * @author jefferyyjhsu@iis.sinica.edu.tw
 */

public class NwaList<LETTER, STATE> implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private static ILogger mLogger;
	ArrayList<INestedWordAutomaton<LETTER, STATE>> automataCollection;

	public NwaList(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> orginalAutomata,
			final INestedWordAutomaton<LETTER, STATE> newAutomata) {
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mLogger.info(startMessage());
		automataCollection = new ArrayList<>();
		automataCollection.add(orginalAutomata);
		automataCollection.add(newAutomata);
		mLogger.info(exitMessage());
	}

	public NwaList(final AutomataLibraryServices services,
			final ArrayList<INestedWordAutomaton<LETTER, STATE>> orginalAutomataCollection,
			final INestedWordAutomaton<LETTER, STATE> newAutomata) {
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mLogger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		mLogger.info(exitMessage());
	}

	public NwaList(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> newAutomata,
			final ArrayList<INestedWordAutomaton<LETTER, STATE>> orginalAutomataCollection) {
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mLogger.info(startMessage());
		automataCollection = orginalAutomataCollection;
		automataCollection.add(newAutomata);
		mLogger.info(exitMessage());
	}

	/**
	 * Constructs a list that consists of a single automaton.
	 */
	public NwaList(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> newAutomata) {
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mLogger.info(startMessage());
		automataCollection = new ArrayList<>();
		automataCollection.add(newAutomata);
		mLogger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "NwaList";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Exit " + operationName();
	}

	@Override
	public ArrayList<INestedWordAutomaton<LETTER, STATE>> getResult() {
		return automataCollection;
	}
	/*public String getResult() throws OperationCanceledException {
		return "NwaList_result:"+automataCollection.size();
	}*/

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

}
