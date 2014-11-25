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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.incremental_inclusion;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ComplementDeterministicNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DeterminizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * This is an implementation of our incremental inclusion check based on a
 * difference construction. This implementation is not efficient and should
 * not used in practice. We use this implementation only for comparison with
 * the "real" incremental inclusion.
 * This implementation could be improved by applying a removal of dead ends
 * and a minimization to the difference after each step.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class InclusionViaDifference<LETTER, STATE> extends
		AbstractIncrementalInclusionCheck<LETTER, STATE> {
	private final  StateFactory<STATE> m_StateFactory;
	private INestedWordAutomatonSimple<LETTER, STATE> m_Difference;

	public InclusionViaDifference(IUltimateServiceProvider services,
			StateFactory<STATE> stateFactory,
			INestedWordAutomatonSimple<LETTER, STATE> a) {
		super(services, a);
		m_StateFactory = stateFactory;
		// initialize difference. B_1,...,B_n is emtpy
		m_Difference = a;
	}

	@Override
	public NestedRun<LETTER, STATE> getCounterexample() throws OperationCanceledException {
		NestedRun<LETTER, STATE> acceptingRun = (new IsEmpty<LETTER, STATE>(m_Difference)).getNestedRun();
		return acceptingRun;
	}

	@Override
	public void addSubtrahend(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		super.addSubtrahend(nwa);
		INestedWordAutomatonSimple<LETTER, STATE> determinized = 
				new DeterminizeNwa<>(nwa, new PowersetDeterminizer<>(nwa, true, m_StateFactory), m_StateFactory);
		INestedWordAutomatonSimple<LETTER, STATE> complemented =
				new ComplementDeterministicNwa<>(determinized);
		INestedWordAutomatonSimple<LETTER, STATE> difference =
				new IntersectNwa<>(m_Difference, complemented, m_StateFactory, false);
		m_Difference = difference;
	}
	

}
