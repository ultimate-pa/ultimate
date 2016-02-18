/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair;

import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;

/**
 * Doc comes later.
 * @author Daniel Tischner
 *
 * @param <LETTER>
 * @param <STATE>
 */
public final class GameGraphSuccessorProvider<LETTER, STATE> implements ISuccessorProvider<Vertex<LETTER, STATE>> {
	
	private FairGameGraph<LETTER, STATE> m_Graph;
	
	public GameGraphSuccessorProvider(FairGameGraph<LETTER, STATE> game) {
		m_Graph = game;
	}

	@Override
	public Iterator<Vertex<LETTER, STATE>> getSuccessors(Vertex<LETTER, STATE> node) {
		if (m_Graph.hasSuccessors(node)) {
			return m_Graph.getSuccessors(node).iterator();
		} else {
			return new HashSet<Vertex<LETTER, STATE>>().iterator();
		}
	}

}
