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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * TODO
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 * 
 *
 * @param <PLACE>
 */
public class OwickiGriesConstruction<LOC extends IcfgLocation, PLACE> {	
	
	private final IPetriNet<IIcfgTransition<LOC>, PLACE> mNet; 	
	private final Map<Marking<IIcfgTransition<LOC>, PLACE>, IPredicate> mFloydHoareAnnotation;
	
	private final OwickiGriesAnnotation<IIcfgTransition<LOC>, PLACE> mAnnotation;	
	private final BasicPredicateFactory mFactory;
	

	public OwickiGriesConstruction(IUltimateServiceProvider services, CfgSmtToolkit csToolkit,
			IPetriNet<IIcfgTransition<LOC>, PLACE> net,
			Map<Marking<IIcfgTransition<LOC>, PLACE>, IPredicate> floydHoare) {			
			mNet = net;	
			mFloydHoareAnnotation = floydHoare;
			mFactory = new BasicPredicateFactory(services, csToolkit.getManagedScript(),
				csToolkit.getSymbolTable());	
			
			mAnnotation = new OwickiGriesAnnotation<>();
			mAnnotation.mGhostVariables = getGhostVariables();
			mAnnotation.mFormulaMapping = getFormulaMapping();
			//TODO: m.Annotation.mAssignmentMapping =
			// mAnnotation.mGhostInitAssignment = getGhostInitAssignment();

			// TODO Code to set variables to false.
			// Similarly for true.
			// Use TransformulaUtils.sequentialComposition to combine.
			//
			// final UnmodifiableTransFormula setToFalse =
			//		TransFormulaBuilder.constructAssignment(new ArrayList<>(variables.values()),
			//				Collections.nCopies(variables.size(), script.term("false")), mSymbolTable, mManagedScript);
	}	 

	/**
	 * Predicate: disjunction of Markings predicate.
	 * Markings predicate: Conjunction of GhostVariable and FH predicate.
	 * @return a Map with a predicate for each place in Net.
	 */	
	public Map<PLACE, IPredicate> getFormulaMapping () {
		Map<PLACE, IPredicate> Mapping = new HashMap<PLACE, IPredicate>();	     
	    for (PLACE place: mNet.getPlaces()) {
	    	Set<IPredicate> Clauses = new HashSet<>();	    	  	
	    	mFloydHoareAnnotation.forEach((key,value)-> {
	    	if(mFloydHoareAnnotation.containsKey(place)) {
	    			Clauses.add(getMarkingPredicate(place, key));}});
	    	Mapping.put(place, mFactory.or(Clauses)); }	    	
		return Mapping;	
	}
	
	/**
	 * @param place
	 * @param marking
	 * @return Predicate with conjunction of Ghost variables and predicate of marking
	 */
	private  IPredicate getMarkingPredicate(PLACE place, Marking<IIcfgTransition<LOC>, PLACE> marking) {
		//TODO: Conjunction of variables not in Marking
		Set<IPredicate> terms =  new HashSet<>(); //Conjunction of GhostVariables of places in marking
		marking.forEach(element -> terms.add(getGhostPredicate(element)));
		terms.add(mFloydHoareAnnotation.get(place)); //Predicate of marking		
		return  mFactory.and(terms);		
	}
	
	/** 
	 * @param place
	 * @return Predicate place's GhostVariable
	 */
	private IPredicate getGhostPredicate(PLACE place) {
	//TODO: Value assignment ??
	 return mFactory.newPredicate(mAnnotation.mGhostVariables.get(place).getTerm());
	 }
	
	/**
	 * @return Map of GhostVariables to Places
	 */
	private Map<PLACE, IProgramVar> getGhostVariables(){
	//TODO: Extend IProgramVar?: name, place, type, value. 
	//TODO: Deal with not place Ghost variables?
		Map<PLACE, IProgramVar> GhostVars = new HashMap<PLACE, IProgramVar>();
		for(PLACE place: mNet.getPlaces()) {
			IProgramVar var = null;			
			// TODO Code to create a new boolean variable.
			//final TermVariable tv =
			//		mManagedScript.constructFreshTermVariable("loc_" + i, SmtSortUtils.getBoolSort(mManagedScript));
			//final IProgramVar var = ProgramVarUtils.constructGlobalProgramVarPair(tv.getName(),
			//		SmtSortUtils.getBoolSort(mManagedScript), mManagedScript, this);
			GhostVars.put(place, var);}
		return GhostVars;
	}
	
	/**
	 * @return set of Initial value assignment of all GhostVariables.
	 */
	private Set<IIcfgTransition<LOC>> getGhostInitAssignment(){		
		Set<IIcfgTransition<LOC>> InitAssignments = new HashSet<>();
		mNet.getInitialPlaces().forEach(place -> InitAssignments.add(getGhostAssignment(place))); //true
		Set<PLACE> NotInit = new HashSet<>(mNet.getPlaces());
		NotInit.removeAll(mNet.getInitialPlaces());
		NotInit.forEach(place -> InitAssignments.add(getGhostAssignment(place))); //false
		return InitAssignments;
	}
	
	/**
	 * 
	 * @param place
	 * @return assignment of the place's GhostVariable.
	 */
	private IIcfgTransition<LOC> getGhostAssignment(PLACE place){
		//TODO: Generate assignment/statement from GhostVar
		IIcfgTransition<LOC> assignment = null;	
		mAnnotation.mGhostVariables.get(place);		
		return assignment;
	}
	
	public OwickiGriesAnnotation<IIcfgTransition<LOC>, PLACE> getResult() {
		return mAnnotation;
	}
	
	
}
