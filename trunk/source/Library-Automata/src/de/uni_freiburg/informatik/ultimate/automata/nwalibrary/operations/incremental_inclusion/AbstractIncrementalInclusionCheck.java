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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * TODO: Documentation
 * 
 * @author Matthias Heizmann
 *
 */
public abstract class AbstractIncrementalInclusionCheck<LETTER,STATE> {
	
	private final IUltimateServiceProvider m_Services;
	
	private final INestedWordAutomatonSimple<LETTER, STATE> m_A;
	private final List<INestedWordAutomatonSimple<LETTER, STATE>> m_B = new ArrayList<>();
	
	
	public AbstractIncrementalInclusionCheck(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER, STATE> a) {
		super();
		m_Services = services;
		m_A = a;
	}


	/**
	 * Return an accepting run of automaton A such that the word of the run is
	 * not accepted by any of the automata B_0,..,B_n.
	 * Return null if no such run exists, i.e., the language inclusion 
	 * A ⊆ B_0 ∪ ... ∪ B_n holds. 
	 * @throws OperationCanceledException 
	 */
	public abstract NestedRun<LETTER,STATE> getCounterexample() throws OperationCanceledException;
	
	
	/**
	 * Add automaton B_{n+1} to our set of subtrahends B_0,...,B_n.
	 * @throws AutomataLibraryException 
	 */
	public void addSubtrahend(INestedWordAutomatonSimple<LETTER, STATE> nwa) throws AutomataLibraryException {
		m_B.add(nwa);
	}
	
	

}
