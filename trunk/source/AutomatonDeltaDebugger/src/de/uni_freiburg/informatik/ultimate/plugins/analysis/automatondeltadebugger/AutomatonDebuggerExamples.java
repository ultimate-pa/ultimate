/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat.MinimizeNwaMaxSAT;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

/**
 * Examples used by delta debugger.
 * 
 * NOTE: Users may insert their sample code as a new method and leave it here.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class AutomatonDebuggerExamples<LETTER, STATE> {
	final private IUltimateServiceProvider mServices;
	
	public AutomatonDebuggerExamples(IUltimateServiceProvider mServices) {
		this.mServices = mServices;
	}
	
	/**
	 * @param automaton automaton
	 * @param factory state factory
	 * @return new <code>MinimizeNwaMaxSAT()</code> instance
	 * @throws Throwable when error occurs
	 */
	public IOperation<LETTER, STATE> MinimizeNwaMaxSAT(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final StateFactory<STATE> factory) throws Throwable {
		return new MinimizeNwaMaxSAT<LETTER, STATE>(
				new AutomataLibraryServices(mServices), factory,
				new RemoveUnreachable<LETTER, STATE>(
						new AutomataLibraryServices(mServices), automaton)
								.getResult());
	}
}