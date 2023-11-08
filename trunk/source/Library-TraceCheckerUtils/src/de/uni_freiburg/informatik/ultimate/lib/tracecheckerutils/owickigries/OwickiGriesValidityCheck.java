/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final Script mScript;

	private final boolean mIsInductive;
	private final boolean mIsInterferenceFree;
	private final boolean mIsProgramSafe;
	private final OwickiGriesAnnotation<LETTER, PLACE> mAnnotation;
	private final Collection<Transition<LETTER, PLACE>> mTransitions;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final BasicPredicateFactory mPredicateFactory;
	private final HashRelation<Transition<LETTER, PLACE>, PLACE> mCoMarkedPlaces;

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final OwickiGriesAnnotation<LETTER, PLACE> annotation,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> coMarkedPlaces) {

		mServices = services;
		mLogger = services.getLoggingService().getLogger(OwickiGriesValidityCheck.class);
		mManagedScript = csToolkit.getManagedScript();
		mScript = csToolkit.getManagedScript().getScript();
		mAnnotation = annotation;
		mPredicateFactory = new BasicPredicateFactory(services, mManagedScript, annotation.getSymbolTable());
		mCoMarkedPlaces = coMarkedPlaces;

		mHoareTripleChecker = new MonolithicHoareTripleChecker(csToolkit);
		mTransitions = mAnnotation.getPetriNet().getTransitions();

		mIsInductive = checkInductivity();
		mIsInterferenceFree = checkInterference();
		mIsProgramSafe = getCfgSafety();
	}

	private boolean checkInductivity() {
		for (final Transition<LETTER, PLACE> transition : mTransitions) {
			if (!getTransitionInductivity(transition)) {
				return false;
			}
		}
		return true;
	}

	private boolean getTransitionInductivity(final Transition<LETTER, PLACE> transition) {
		final Set<PLACE> predecessors = transition.getPredecessors();
		for (final PLACE pre : predecessors) {
			mLogger.info(getPlacePredicate(pre));
		}
		final IPredicate precondition = getConjunctionPredicate(predecessors);
		final IPredicate postcondition = getConjunctionPredicate(transition.getSuccessors());
		return mHoareTripleChecker.checkInternal(precondition, getTransitionSeqAction(transition),
				postcondition) == Validity.VALID;
	}

	private IPredicate getConjunctionPredicate(final Set<PLACE> places) {
		final Collection<IPredicate> predicates = new HashSet<>();
		for (final PLACE place : places) {
			predicates.add(getPlacePredicate(place));
		}
		return mPredicateFactory.and(predicates);
	}

	private IInternalAction getTransitionSeqAction(final Transition<LETTER, PLACE> transition) {
		final List<UnmodifiableTransFormula> actions = Arrays.asList(transition.getSymbol().getTransformula(),
				mAnnotation.getAssignmentMapping().get(transition));
		return new BasicInternalAction(null, null, TransFormulaUtils.sequentialComposition(mLogger, mServices,
				mManagedScript, false, false, false, null, null, actions));
	}

	private IPredicate getPlacePredicate(final PLACE Place) {
		return mAnnotation.getFormulaMapping().get(Place);
	}

	private boolean checkInterference() {
		for (final Transition<LETTER, PLACE> transition : mTransitions) {
			if (!getTransitionInterFree(transition)) {
				return false;
			}
		}
		return true;
	}

	private boolean getTransitionInterFree(final Transition<LETTER, PLACE> transition) {
		final IPredicate predecessorsPred = getConjunctionPredicate(transition.getPredecessors());
		final IInternalAction action = getTransitionSeqAction(transition);
		final Set<PLACE> coMarked = getComarkedPlaces(transition);
		for (final PLACE place : coMarked) {
			if (!getInterferenceFreeTriple(predecessorsPred, action, place)) {
				return false;
			}
		}
		return true;
	}

	private Set<PLACE> getComarkedPlaces(final Transition<LETTER, PLACE> transition) {
		return mCoMarkedPlaces.getImage(transition);
	}

	/**
	 *
	 * @param Pred
	 * @param Action
	 * @param place
	 * @return Validity of Interference Freedom of Transition wrt co-marked place
	 */
	private boolean getInterferenceFreeTriple(final IPredicate Pred, final IInternalAction Action, final PLACE place) {
		final IPredicate placePred = getPlacePredicate(place);
		final List<IPredicate> predicate = Arrays.asList(Pred, placePred);
		return mHoareTripleChecker.checkInternal(mPredicateFactory.and(predicate), Action, placePred) == Validity.VALID;
	}

	// TODO:find better name
	private boolean getCfgSafety() {
		if (!getInitImplication() || !getAcceptFormula()) {
			return false;
		}
		return true;
	}

	private boolean getInitImplication() {
		final IPredicate initFormula = getInitFormula();
		final MonolithicImplicationChecker checker = new MonolithicImplicationChecker(mServices, mManagedScript);
		for (final PLACE place : mAnnotation.getPetriNet().getInitialPlaces()) {
			if (Validity.VALID != checker.checkImplication(initFormula, false, getPlacePredicate(place), false)) {
				return false;
			}
		}
		return true;
	}

	private IPredicate getInitFormula() {
		final List<IPredicate> terms = new ArrayList<>();
		for (final IProgramVar var : mAnnotation.getGhostAssignment().keySet()) {
			terms.add(mPredicateFactory.newPredicate(
					SmtUtils.binaryEquality(mScript, var.getTerm(), mAnnotation.getGhostAssignment().get(var))));
		}
		return mPredicateFactory.and(terms);
	}

	private boolean getAcceptFormula() {
		for (final PLACE place : mAnnotation.getPetriNet().getAcceptingPlaces()) {
			// TODO: Ask about this or checkSatEquivalence
			if (LBool.UNSAT != SmtUtils.checkSatTerm(mScript, getPlacePredicate(place).getFormula())) {
				return false;
			}
		}
		return true;
	}

	public boolean isValid() {
		return mIsInductive && mIsInterferenceFree && mIsProgramSafe;
	}
}
