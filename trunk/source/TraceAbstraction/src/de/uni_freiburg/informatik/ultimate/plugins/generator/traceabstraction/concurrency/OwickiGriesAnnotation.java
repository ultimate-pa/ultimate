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

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
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

	 //Petri net 
	private final IPetriNet<LETTER, PLACE> mPetriNet;

	/**
	 * Omega: maps Predicate -> Place
	 */
	private final Map<PLACE, IPredicate> mFormulaMapping;
	
	/**
	 * Gamma: maps GhostAssignment -> transition
	 */
	private final Map<ITransition<LETTER,PLACE>, UnmodifiableTransFormula> mAssignmentMapping;
	
	/**
	 * VGhost: maps Ghost Variables to set
	 */	
	//TODO: Map or Set? Map might be only needed for Construction
	private final Map<PLACE, IProgramVar>  mGhostVariables;
	
	/**
	 * rho(VGhost):  set of predicate value -> GhostVariables
	 */
	//protected Map<ITransition<LETTER,PLACE>,LETTER> mGhostAssignment;
	private final Set<UnmodifiableTransFormula> mGhostInitAssignment;

	public OwickiGriesAnnotation() {
		mPetriNet = null;
		mFormulaMapping = null;
		mAssignmentMapping = null;
		mGhostVariables = null;
		mGhostInitAssignment = null;	
		
	}
	
	/**
	 * Constructor
	 * @param FormulaMapping
	 * @param AssignmentMapping
	 * @param GhostVariables
	 * @param GhostInitAssignment
	 * @param net
	 */
	public  OwickiGriesAnnotation
	(Map<PLACE, IPredicate> FormulaMapping, Map<ITransition<LETTER,PLACE>, UnmodifiableTransFormula> AssignmentMapping,
			Map<PLACE, IProgramVar> GhostVariables, Set<UnmodifiableTransFormula> GhostInitAssignment,
			IPetriNet<LETTER, PLACE> net) {
		mFormulaMapping = FormulaMapping;
		mAssignmentMapping = AssignmentMapping;
		mGhostVariables = GhostVariables;
		mGhostInitAssignment = GhostInitAssignment;
		mPetriNet = net;
	}
	
	public Map<PLACE, IPredicate> getFormulaMapping() {
		return mFormulaMapping;
	}
	
	public Map<ITransition<LETTER,PLACE>, UnmodifiableTransFormula> getAssignmentMapping(){
		return mAssignmentMapping;
	}
	
	public Map<PLACE, IProgramVar> GhostVariables(){
		return mGhostVariables;
	}
	
	public  Set<UnmodifiableTransFormula> getGhostAssignment(){
		return mGhostInitAssignment;
	}
	
	public IPetriNet<LETTER, PLACE> getPetriNet(){
		return mPetriNet;
	}
	
	
	
	//TODO: define OGAnnotation Size
	public int getSize() {
		// ...
		return 0;
	}
	
}
