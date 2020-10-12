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


import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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
public class OwickiGriesConstruction<LOC extends IcfgLocation, PLACE, LETTER > {	
	
	private final IPetriNet<LETTER, PLACE> mNet; 	
	private final Map<Marking<LETTER, PLACE>, IPredicate> mFloydHoareAnnotation;
	
	private final OwickiGriesAnnotation<LETTER, PLACE> mAnnotation;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final BasicPredicateFactory mFactory;
	private final ILogger mLogger;
	private final IIcfgSymbolTable mSymbolTable;
	private final static SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final static XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	
	//Variables for Annotation construction
	private final Map<PLACE, IProgramVar> mGhostVariables;
	private final Map<PLACE, IPredicate> mFormulaMappingD;
	private final Map<IProgramVar, Term> mGhostInitAssignment;
	private final Map<ITransition<LETTER, PLACE>, UnmodifiableTransFormula> mAssignmentMapping;
	
	
	public OwickiGriesConstruction(IUltimateServiceProvider services, CfgSmtToolkit csToolkit,
			IPetriNet<LETTER, PLACE> net,
			Map<Marking<LETTER, PLACE>, IPredicate> floydHoare) {			
			mNet = net;				
			mFloydHoareAnnotation = floydHoare;			
			mScript =  csToolkit.getManagedScript().getScript();
			mManagedScript = csToolkit.getManagedScript();
			mSymbolTable = csToolkit.getSymbolTable();
			mServices = services;
			mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
			mFactory = new BasicPredicateFactory(mServices, mManagedScript,
				csToolkit.getSymbolTable());			
			
			mGhostVariables = getGhostVariables();
			mFormulaMappingD = getFormulaMapping();				
			mAssignmentMapping = getAssignmentMapping();
			mGhostInitAssignment = getGhostInitAssignment();
			
			mAnnotation = new OwickiGriesAnnotation<LETTER, PLACE> (mFormulaMappingD, mAssignmentMapping, 
					mGhostVariables, mGhostInitAssignment, mNet);		
	}	 

	/**
	 * Predicate: disjunction of Markings predicate.
	 * Markings predicate: Conjunction of All GhostVariable and FH predicate.
	 * @return a Map with a predicate for each place in Net.
	 */	
	public Map<PLACE, IPredicate> getFormulaMapping() {
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
	private  IPredicate getMarkingPredicate(PLACE place, Marking<LETTER, PLACE> marking) {
		//TODO:Formula Type: Conjunction and Implication				
		Set<IPredicate> terms =  new HashSet<>(); 
		marking.forEach(element -> terms.add(getGhostPredicate(element))); //GhostVariables of places in marking		
		terms.addAll(getSubsetMarking(marking)); //OptionB: getAllNotMarking; OptionA: getSubsetMarking;
		terms.add(mFloydHoareAnnotation.get(place)); //Predicate of marking	
		return  mFactory.and(terms);		
	}

	/**
	 * 
	 * @param marking
	 * @return Formula MethodB:Predicate with GhostVariables of all other places not in marking
	 */
	private Set<IPredicate> getAllNotMarking(Marking<LETTER, PLACE> marking){
		Set<IPredicate> predicates = new HashSet<>();
	    Collection<PLACE> notMarking = mNet.getPlaces();
		notMarking.removeAll(marking.stream().collect(Collectors.toSet()));		
	    notMarking.forEach(element -> predicates.add(mFactory.not(getGhostPredicate(element))));
	    return predicates;		
	}
	
	/**
	 * 
	 * @param marking
	 * @return Formula MethodA: GhostVariables if marking is subset of other marking
	 */
	private Set<IPredicate> getSubsetMarking(Marking<LETTER, PLACE> marking){
		Set<PLACE> markPlaces = marking.stream().collect(Collectors.toSet()); 
		Set<Marking<LETTER, PLACE>> Markings = mFloydHoareAnnotation.keySet();	
		Collection<PLACE> notMarking = new HashSet<>();
		Markings.forEach(otherMarking -> notMarking.addAll(getSupPlaces(otherMarking, markPlaces)));
		Set<IPredicate> predicates = new HashSet<>();	    
	    notMarking.forEach(element -> predicates.add(mFactory.not(getGhostPredicate(element))));
	    return predicates;		
	}
	
	private Collection<PLACE> getSupPlaces(Marking<LETTER, PLACE> otherMarking, Set<PLACE> markPlaces){
		Collection<PLACE> SubPlaces = new HashSet<>();
		Set<PLACE> otherPlaces = otherMarking.stream().collect(Collectors.toSet()); 
		if (otherPlaces.containsAll(markPlaces)) {
			otherPlaces.removeAll(markPlaces);
			SubPlaces.addAll(otherPlaces);}		
		return SubPlaces;
	}

	
	/** 
	 * @param place
	 * @return Predicate place's GhostVariable
	 */
	private IPredicate getGhostPredicate(PLACE place) {
	  return mFactory.newPredicate(mGhostVariables.get(place).getTerm());
	 }
	
	/**
	 * @return Map of GhostVariables to Places
	 */
	private Map<PLACE, IProgramVar> getGhostVariables(){
		Map<PLACE, IProgramVar> GhostVars = new HashMap<PLACE, IProgramVar>();
		int i = 0;
		Collection<PLACE> places = mNet.getPlaces(); 
		for(PLACE place: places) {
			final TermVariable tVar = mManagedScript.constructFreshTermVariable
					("np_" + i, SmtSortUtils.getBoolSort(mManagedScript));
			final IProgramVar pVar = ProgramVarUtils.constructGlobalProgramVarPair
					(tVar.getName(), SmtSortUtils.getBoolSort(mManagedScript), mManagedScript, this);	
			GhostVars.put(place, pVar);
			i++;
		}
		return GhostVars;
	}
	
	/**
	 * @return set of Initial value assignment of all GhostVariables.
	 * 
	 */
	private Map<IProgramVar, Term> getGhostInitAssignment(){
		HashMap<IProgramVar, Term> InitAssignments = new HashMap<IProgramVar,  Term>();		
		Set<IProgramVar> InitGhostVariables = new HashSet<IProgramVar>();//Get all GhostVariables from Initial places
		Set<PLACE> Places = mNet.getInitialPlaces();
		Places.forEach(place -> 
			InitGhostVariables.add(mGhostVariables.get(place)));		
		InitGhostVariables.stream().forEach(variable -> InitAssignments.put(variable, mScript.term("true")));	
		Collection<IProgramVar> NotInitGhostVariables =	mGhostVariables.values();
		NotInitGhostVariables.removeAll(InitGhostVariables);//Ghost variables of not Initial places
		NotInitGhostVariables.forEach(variable -> InitAssignments.put(variable, mScript.term("false")));
		return InitAssignments;
	}
	
	/**
	 * 
	 * @param place
	 * @return assignment of the place's GhostVariable.
	 */
	private UnmodifiableTransFormula getGhostAssignment(Collection<IProgramVar> vars, String term){
		return  TransFormulaBuilder.constructAssignment(new ArrayList<>(vars),
						Collections.nCopies(vars.size(), mScript.term(term)), mSymbolTable, mManagedScript);
	}	

	/**
	 * 
	 * @return Map of Places' Ghost Variables assignments to Transitions
	 * 
	 */	
	private Map<ITransition<LETTER, PLACE>,UnmodifiableTransFormula> getAssignmentMapping(){
		Map<ITransition<LETTER,PLACE>,UnmodifiableTransFormula> AssignmentMapping = 
				new HashMap <ITransition<LETTER,PLACE>, UnmodifiableTransFormula>();
		Collection<ITransition<LETTER,PLACE>> Transitions = mNet.getTransitions();
		Transitions.forEach(transition -> AssignmentMapping.put(transition, getTransitionAssignment(transition)));				
		return AssignmentMapping;
	}
	
	/**
	 * 
	 * @param transition
	 * @return TransFormula of sequential compositions of GhostVariables assignments.
	 * GhostVariables of Predecessors Places are assign to false,
	 * GhostVariables of Successors Places are assign to true.
	 */
	private UnmodifiableTransFormula getTransitionAssignment(ITransition<LETTER,PLACE> transition) {			
		List<UnmodifiableTransFormula> assignments = new ArrayList<>();
		Set<PLACE> Places = mNet.getPredecessors(transition);
		Places.forEach(place -> {
			IProgramVar var = mGhostVariables.get(place);
			assignments.add
				(getGhostAssignment(Collections.nCopies(1,var),"false"));});
		Places = mNet.getSuccessors(transition);	
		Places.forEach(place -> assignments.add
				(getGhostAssignment(Collections.nCopies(1,mGhostVariables.get(place)),"true")));
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, 
				false, false, false, mXnfConversionTechnique, mSimplificationTechnique, assignments);			
	}
	
	public OwickiGriesAnnotation<LETTER, PLACE> getResult() {
		return mAnnotation;
	}
	
	
}
