/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Map;
import java.util.Set;
import java.util.Collection;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * TODO
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class OwickiGriesAnnotation<LETTER, PLACE> {

	// Petri net
	private final IPetriNet<LETTER, PLACE> mPetriNet;

	//Omega: Predicate -> Place
	private final Map<PLACE, IPredicate> mFormulaMapping;
	
	//Gamma: GhostAssignment -> transition
	private final Map<ITransition<LETTER,PLACE>, LETTER> mAssignmentMapping;
	
	//VGhost: set of Ghost Variables
	private final Set<IProgramVar> mGhostVariables;
	
	//rho(VGhost): value -> GhostVariables
	private final Map<ITransition,LETTER> mGhostAssignment;

	public OwickiGriesAnnotation() {
		mPetriNet = null;
		mFormulaMapping = null;
		mAssignmentMapping = null;
		mGhostVariables = null;
		mGhostAssignment = null;	
		
	}

	public int getSize() {
		// ...
		return 0;
	}
}
