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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;

/**
 * Minimization method which returns an #{@link IDoubleDeckerAutomaton} as result.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class AbstractMinimizeNwaDd<LETTER, STATE> extends AbstractMinimizeNwa<LETTER, STATE> {
	/**
	 * This constructor should be called by all subclasses and only by them.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 */
	protected AbstractMinimizeNwaDd(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory) {
		super(services, stateFactory);
	}

	/**
	 * @return Result as {@link IDoubleDeckerAutomaton}.
	 */
	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		final INestedWordAutomaton<LETTER, STATE> result = super.getResult();
		assert result instanceof IDoubleDeckerAutomaton : "The result constructed must be an IDoubleDeckerAutomaton.";
		return (IDoubleDeckerAutomaton<LETTER, STATE>) result;
	}
}
