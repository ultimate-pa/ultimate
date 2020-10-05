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
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
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
	private final Collection<ITransition<LETTER, PLACE>> mTransitions;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final BasicPredicateFactory mPredicateFactory;
	

	public OwickiGriesValidityCheck(IUltimateServiceProvider services, CfgSmtToolkit csToolkit,
			OwickiGriesAnnotation<LETTER, PLACE> annotation) {
		
		mServices = services;
		mManagedScript = csToolkit.getManagedScript();
		mAnnotation = annotation;
		mPredicateFactory = new BasicPredicateFactory(services, mManagedScript,
				csToolkit.getSymbolTable());
		
		mHoareTripleChecker = new MonolithicHoareTripleChecker(csToolkit);
		mTransitions =  mAnnotation.getPetriNet().getTransitions();		

		mIsInductive = checkInductivity(); // TODO: finish predicates of Pred and Succ
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
		Set<PLACE> Predecessors = mAnnotation.getPetriNet().getPredecessors(Transition),
				Successors = mAnnotation.getPetriNet().getSuccessors(Transition);
		Collection<IPredicate> preds = new HashSet<>(), succs = new HashSet<>();
		Predecessors.stream().forEach(pred -> preds.add(getPlacePredicate(pred)));
		Successors.stream().forEach(succ -> succs.add(getPlacePredicate(succ)));
		IPredicate Pred = mPredicateFactory.and(preds),
				  Succ = mPredicateFactory.and(succs);
		List<UnmodifiableTransFormula> actions = new ArrayList<>();
		actions.add((UnmodifiableTransFormula) Transition.getSymbol());
		actions.add((UnmodifiableTransFormula) mAnnotation.getAssignmentMapping().get(Transition));		
		IInternalAction Act = new BasicInternalAction
				(null, null, TransFormulaUtils.sequentialComposition
						(null, mServices, mManagedScript,false, false, false, null, null, actions));		
		return getValidityResult(mHoareTripleChecker.checkInternal(Pred, Act, Succ));	
	}
	
	private IPredicate getPlacePredicate(PLACE Place) {
		//TODO: Get Term from Place and replace null
		return  mPredicateFactory.newPredicate(null);
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
	/*
	 * private boolean getTransitionInd(ITransition<LETTER, PLACE> Transition) {
	 * Set<PLACE> Predecessors =
	 * mAnnotation.getPetriNet().getPredecessors(Transition); if
	 * (Predecessors.stream().filter(pred -> !checkTripleInd(Transition,
	 * pred)).count() >= 1) return false; return true; } private boolean
	 * checkTripleInd(ITransition<LETTER, PLACE> Transition, PLACE Predecessor) {
	 * Set<PLACE> Succesors = mAnnotation.getPetriNet().getSuccessors(Transition);
	 * if (Succesors.stream().filter(succ -> !getHoareTripleVal(Transition,
	 * Predecessor, succ)).count() >= 1) return false; return true; }
	 * 
	 * private boolean getHoareTripleVal(ITransition<LETTER, PLACE> Transition,
	 * PLACE Predecessor, PLACE Successor) { //TODO: replace nulls with terms from
	 * PLACE Predecessor and Successor -> //Find where is the the formula "assigned"
	 * to Place in PetriNet? IPredicate Pred = mPredicateFactory.newPredicate(null);
	 * IPredicate Succ = mPredicateFactory.newPredicate(null);
	 * List<UnmodifiableTransFormula> actions = new ArrayList<>();
	 * actions.add((UnmodifiableTransFormula) Transition.getSymbol());
	 * actions.add((UnmodifiableTransFormula)
	 * mAnnotation.getAssignmentMapping().get(Transition)); IInternalAction Act =
	 * new BasicInternalAction (null, null, TransFormulaUtils.sequentialComposition
	 * (null, mServices, mManagedScript,false, false, false, null, null, actions));
	 * mHoareTripleChecker.checkInternal(Pred, Act, Succ); return false; }
	 */
	
	
	private boolean checkInterference() {
		//Check Interference Freedom of each transition
			//For each transition ->
				//Get co-marked places of transition (steps in notes)
				//getConjuntion of all transition predecessors' predicate
				//getAction: PetriNet Action; GhostAssignments
				//For each co-marked place -> getInterferenceFreeHoareTriple
					//getPlacesPred
					//checkHoareTriple(Conjunction of pred and Pred(comarkplace), Action, ) 
		
		return false;
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
		return true;
	}

	
	public boolean isValid() {
		return mIsInductive && mIsInterferenceFree;
	}
}
