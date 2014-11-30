/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.AbstractIntersect;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class BuchiIntersectDD<LETTER, STATE> extends
		AbstractIntersect<LETTER, STATE> implements IOperation<LETTER,STATE> {

	public BuchiIntersectDD(IUltimateServiceProvider services,
			INestedWordAutomatonOldApi<LETTER, STATE> fstNwa,
			INestedWordAutomatonOldApi<LETTER, STATE> sndNwa)
			throws AutomataLibraryException {
		super(services, true, false, fstNwa, sndNwa);
	}

	public BuchiIntersectDD(IUltimateServiceProvider services,
			INestedWordAutomatonOldApi<LETTER, STATE> fstNwa,
			INestedWordAutomatonOldApi<LETTER, STATE> sndNwa,
			boolean minimizeResult)
			throws AutomataLibraryException {
		super(services, true, minimizeResult, fstNwa, sndNwa);
	}

	@Override
	public String operationName() {
		return "buchiIntersectDD";
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
