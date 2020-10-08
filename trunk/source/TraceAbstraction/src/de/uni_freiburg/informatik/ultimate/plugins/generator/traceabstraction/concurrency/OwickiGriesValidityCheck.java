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

import java.util.List;
import java.util.Map;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 * TODO
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <PLACE>
 */
public class OwickiGriesValidityCheck<LETTER extends IAction, PLACE> {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	
	private final boolean mIsInductive;
	private final boolean mIsInterferenceFree;
	private final OwickiGriesAnnotation<LETTER, PLACE> mAnnotation;
	private final Map<Marking<LETTER, PLACE>, IPredicate> mFloydHoareAnnotation;
	private final Collection<ITransition<LETTER, PLACE>> mTransitions;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final BasicPredicateFactory mPredicateFactory;
	

	public OwickiGriesValidityCheck(IUltimateServiceProvider services, CfgSmtToolkit csToolkit,
			OwickiGriesAnnotation<LETTER, PLACE> annotation, Map<Marking<LETTER, PLACE>, IPredicate> FloydHoareAnnotation) {
		
		mServices = services;
		mManagedScript = csToolkit.getManagedScript();
		mFloydHoareAnnotation = FloydHoareAnnotation;
		mAnnotation = annotation;
		mPredicateFactory = new BasicPredicateFactory(services, mManagedScript,
				csToolkit.getSymbolTable());
		
		mHoareTripleChecker = new MonolithicHoareTripleChecker(csToolkit);
		mTransitions =  mAnnotation.getPetriNet().getTransitions();		

		mIsInductive = checkInductivity(); 
		mIsInterferenceFree = checkInterference(); // TODO
	}
	
	private boolean checkInductivity() {		
		//TODO: check this line code
		if(mTransitions.stream().filter(transition -> 
			!getTransitionInductivity(transition)).count() >= 1)
			{return false;}
		return true;
	}
	
	private boolean getTransitionInductivity(ITransition<LETTER, PLACE> Transition) {			
		return getValidityResult(mHoareTripleChecker.checkInternal
				(getConjunctionPredicate(mAnnotation.getPetriNet().getPredecessors(Transition)),
						getTransitionSeqAction(Transition), 
				getConjunctionPredicate(mAnnotation.getPetriNet().getSuccessors(Transition))));	
	}
	
	private IPredicate getConjunctionPredicate(Set<PLACE> set) {
		Collection<IPredicate> predicates = new HashSet<>();
		set.stream().forEach(element -> predicates.add(getPlacePredicate(element)));
		return mPredicateFactory.and(predicates);
	}
	
	private IInternalAction getTransitionSeqAction(ITransition<LETTER, PLACE> Transition) {
		List<UnmodifiableTransFormula> actions = Arrays.asList(
				(UnmodifiableTransFormula)Transition.getSymbol(),
				(UnmodifiableTransFormula) mAnnotation.getAssignmentMapping().get(Transition) );
		return new BasicInternalAction
				(null, null, TransFormulaUtils.sequentialComposition
						(null, mServices, mManagedScript,false, false, false, null, null, actions));
	}
	
	private IPredicate getPlacePredicate(PLACE Place) {
		return  mAnnotation.getFormulaMapping().get(Place);
	}
	
	private boolean getValidityResult(Validity validity) {
		final boolean result;
		if (validity == Validity.VALID) {
			result = true;
		} else {
			result = false;
		}
		return result;
	}
		
	private boolean checkInterference() {		
		if(mTransitions.stream().filter(transition -> 
		!getTransitionInterFree(transition)).count() >= 1)
			return false;
		return true;	
	}

	private boolean getTransitionInterFree(ITransition<LETTER, PLACE> Transition) {
		 IPredicate PredecessorsPred = getConjunctionPredicate(mAnnotation.getPetriNet().getPredecessors(Transition));
		 IInternalAction Action = getTransitionSeqAction(Transition);
		 Set<PLACE> Comarked = getComarkedPlaces(Transition);
		 if (Comarked.stream().filter(place -> !getInterferenceFreeTriple(PredecessorsPred, Action, place )).count() >= 1)
			 return false;
		return true;
	}
	
	private Set<PLACE> getComarkedPlaces(ITransition<LETTER,PLACE> Transition){
		Set<PLACE> Predecessors = mAnnotation.getPetriNet().getPredecessors(Transition),
				  comarked = new HashSet<>(); 
		//Reachable Markings in which transition is enabled: All predecessors of transition is in Marking		
		Set<Marking<LETTER,PLACE>> enabledMarkings = 
				 mFloydHoareAnnotation.keySet().stream().filter(marking ->
				marking.containsAll(Predecessors)).collect(Collectors.toSet());
		//places in markings
		enabledMarkings.stream().forEach(marking -> 
			   comarked.addAll(marking.stream().collect(Collectors.toSet())));
		//places that are not predecessors of transition
		comarked.removeAll(Predecessors);
		return comarked;
	}
	
	/**
	 * 
	 * @param Pred
	 * @param Action
	 * @param place
	 * @return Validity of Interference Freedom of Transition wrt co-marked place
	 */
	private boolean getInterferenceFreeTriple(IPredicate Pred, IInternalAction Action, PLACE place) {
		IPredicate placePred = getPlacePredicate(place);
		List<IPredicate> predicate = Arrays.asList(Pred,placePred);		
		return getValidityResult(mHoareTripleChecker.checkInternal
				(mPredicateFactory.and(predicate), Action, placePred));	
	}

	
	public boolean isValid() {
		return mIsInductive && mIsInterferenceFree;
	}
}
