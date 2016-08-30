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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class LassoExtractor<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mReach;
	
	private final List<NestedLassoRun<LETTER, STATE>> mNestedLassoRuns;
	private final List<NestedLassoWord<LETTER>> mNestedLassoWords;
	
	public LassoExtractor(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> operand) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = operand;
		mLogger.info(startMessage());
		if (mOperand instanceof NestedWordAutomatonReachableStates) {
			mReach = (NestedWordAutomatonReachableStates<LETTER, STATE>) mOperand;
		} else {
			mReach = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mOperand);
		}
		mReach.getOrComputeAcceptingComponents();
		mNestedLassoRuns = mReach.getOrComputeAcceptingComponents().getAllNestedLassoRuns();
		mNestedLassoWords = new ArrayList<NestedLassoWord<LETTER>>(mNestedLassoRuns.size());
		if (mNestedLassoRuns.isEmpty() && mReach.getOrComputeAcceptingComponents().getNestedLassoRun() == null) {
			assert (new BuchiIsEmpty<LETTER, STATE>(mServices, mReach)).getResult();
		} else {
			for (final NestedLassoRun<LETTER, STATE> nlr : mNestedLassoRuns) {
				mNestedLassoWords.add(nlr.getNestedLassoWord());
			}
		}
		mLogger.info(exitMessage());
	}
	
	@Override
	public List<NestedLassoWord<LETTER>> getResult() {
		return mNestedLassoWords;
	}
	
	@Override
	public String operationName() {
		return "getSomeAcceptedLassoRuns";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand "
				+ mOperand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Found " + mNestedLassoRuns.size() + " examples of accepted words.";
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}
	
}
