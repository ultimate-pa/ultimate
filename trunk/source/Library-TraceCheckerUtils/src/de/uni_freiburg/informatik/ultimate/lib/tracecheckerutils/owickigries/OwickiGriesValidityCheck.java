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
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.CnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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

	private final Validity mIsInductive;
	private final Validity mIsInterferenceFree;
	private final Validity mIsProgramSafe;

	private final OwickiGriesAnnotation<LETTER, PLACE> mAnnotation;
	private final Collection<Transition<LETTER, PLACE>> mTransitions;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final BasicPredicateFactory mPredicateFactory;
	private final HashRelation<Transition<LETTER, PLACE>, PLACE> mCoMarkedPlaces;

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final OwickiGriesAnnotation<LETTER, PLACE> annotation,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> coMarkedPlaces) {
		this(services, csToolkit.getManagedScript(), new MonolithicHoareTripleChecker(csToolkit), annotation,
				coMarkedPlaces);
	}

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final ModifiableGlobalsTable modifiableGlobals, final OwickiGriesAnnotation<LETTER, PLACE> annotation,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> coMarkedPlaces) {
		this(services, mgdScript, new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals), annotation,
				coMarkedPlaces);
	}

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker htc, final OwickiGriesAnnotation<LETTER, PLACE> annotation,
			final HashRelation<Transition<LETTER, PLACE>, PLACE> coMarkedPlaces) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(OwickiGriesValidityCheck.class);
		mManagedScript = mgdScript;
		mScript = mgdScript.getScript();
		mAnnotation = annotation;
		mPredicateFactory = new BasicPredicateFactory(services, mManagedScript, annotation.getSymbolTable());
		mCoMarkedPlaces = coMarkedPlaces;

		mHoareTripleChecker = htc;
		mTransitions = mAnnotation.getPetriNet().getTransitions();

		mIsInductive = checkInductivity();
		mIsInterferenceFree = checkNonInterference();
		mIsProgramSafe = checkSafety();
	}

	private Validity checkInductivity() {
		Validity result = Validity.VALID;
		for (final Transition<LETTER, PLACE> transition : mTransitions) {
			final var check = isInductive(transition);
			result = result.and(check);

			if (result == Validity.INVALID) {
				break;
			}
		}
		return result;
	}

	private Validity isInductive(final Transition<LETTER, PLACE> transition) {
		final var precondition = getConjunctionPredicate(transition.getPredecessors());
		final var postcondition = getConjunctionPredicate(transition.getSuccessors());
		final var composedAction = getTransitionSeqAction(transition);

		final var inductivity = mHoareTripleChecker.checkInternal(precondition, composedAction, postcondition);
		if (inductivity == Validity.INVALID) {
			final var simplePre = SmtUtils.simplify(mManagedScript, precondition.getFormula(), mServices,
					SimplificationTechnique.SIMPLIFY_DDA);
			final var cnfPre = new CnfTransformer(mManagedScript, mServices).transform(simplePre);
			final var verySimplePre =
					SmtUtils.simplify(mManagedScript, cnfPre, mServices, SimplificationTechnique.SIMPLIFY_DDA);

			final var simplePost = SmtUtils.simplify(mManagedScript, postcondition.getFormula(), mServices,
					SimplificationTechnique.SIMPLIFY_DDA);
			final var cnfPost = new CnfTransformer(mManagedScript, mServices).transform(simplePost);
			final var verySimplePost =
					SmtUtils.simplify(mManagedScript, cnfPost, mServices, SimplificationTechnique.SIMPLIFY_DDA);

			mLogger.warn(
					"Non-inductive transition %s. Invalid Hoare triple:\n"
							+ "\tprecondition %s\n\ttransition %s\n\tpostcondition %s",
					transition, verySimplePre.toStringDirect(), composedAction, verySimplePost.toStringDirect());
		}

		return inductivity;
	}

	private Validity checkNonInterference() {
		Validity result = Validity.VALID;

		for (final Transition<LETTER, PLACE> transition : mTransitions) {
			final var check = isInterferenceFree(transition);
			result = result.and(check);

			if (result == Validity.INVALID) {
				break;
			}
		}
		return result;
	}

	private Validity isInterferenceFree(final Transition<LETTER, PLACE> transition) {
		final var precondition = getConjunctionPredicate(transition.getPredecessors());
		final var composedAction = getTransitionSeqAction(transition);

		Validity result = Validity.VALID;
		for (final PLACE place : getComarkedPlaces(transition)) {
			final var check = isInterferenceFreeForPlace(transition, precondition, composedAction, place);
			result = result.and(check);

			if (result == Validity.INVALID) {
				break;
			}
		}
		return result;
	}

	private Validity isInterferenceFreeForPlace(final Transition<LETTER, PLACE> transition,
			final IPredicate precondition, final IInternalAction action, final PLACE place) {
		final IPredicate placePred = getPlacePredicate(place);
		final List<IPredicate> predicate = Arrays.asList(precondition, placePred);

		final var result = mHoareTripleChecker.checkInternal(mPredicateFactory.and(predicate), action, placePred);
		if (result == Validity.INVALID) {
			mLogger.warn(
					"Transition %s interferes with annotation of place %s. Invalid Hoare triple:\n"
							+ "\tprecondition %s\n\ttransition %s\n\tpostcondition %s",
					transition, place, precondition, action, predicate);
		}

		return result;
	}

	private IPredicate getConjunctionPredicate(final Set<PLACE> places) {
		return mPredicateFactory.and(places.stream().map(this::getPlacePredicate).collect(Collectors.toSet()));
	}

	private IPredicate getPlacePredicate(final PLACE place) {
		return mAnnotation.getFormulaMapping().get(place);
	}

	private IInternalAction getTransitionSeqAction(final Transition<LETTER, PLACE> transition) {
		final var ghostUpdate = mAnnotation.getAssignmentMapping().get(transition);
		final var ghostTransition = ghostUpdate.makeTransitionFormula(mManagedScript, mAnnotation.getSymbolTable());
		final var actions = Arrays.asList(transition.getSymbol().getTransformula(), ghostTransition);
		return new BasicInternalAction(null, null, TransFormulaUtils.sequentialComposition(mLogger, mServices,
				mManagedScript, false, false, false, null, null, actions));
	}

	private Set<PLACE> getComarkedPlaces(final Transition<LETTER, PLACE> transition) {
		return mCoMarkedPlaces.getImage(transition);
	}

	private Validity checkSafety() {
		final var preImpliesInitial = checkInitImplication();
		if (preImpliesInitial == Validity.INVALID) {
			return preImpliesInitial;
		}

		return preImpliesInitial.and(checkAcceptFormula());
	}

	private Validity checkInitImplication() {
		final IPredicate initFormula = getInitFormula();
		final MonolithicImplicationChecker checker = new MonolithicImplicationChecker(mServices, mManagedScript);

		Validity result = Validity.VALID;
		for (final PLACE place : mAnnotation.getPetriNet().getInitialPlaces()) {
			final var predicate = getPlacePredicate(place);
			final var check = checker.checkImplication(initFormula, false, predicate, false);
			result = result.and(check);

			if (result == Validity.INVALID) {
				mLogger.warn("Annotation %s of initial place %s not implied by ghost variable initialization %s",
						predicate, place, initFormula);
				break;
			}
		}
		return result;
	}

	private IPredicate getInitFormula() {
		final List<IPredicate> terms = new ArrayList<>();
		for (final IProgramVar var : mAnnotation.getGhostAssignment().keySet()) {
			terms.add(mPredicateFactory.newPredicate(
					SmtUtils.binaryEquality(mScript, var.getTerm(), mAnnotation.getGhostAssignment().get(var))));
		}
		return mPredicateFactory.and(terms);
	}

	private Validity checkAcceptFormula() {
		Validity result = Validity.VALID;
		for (final PLACE place : mAnnotation.getPetriNet().getAcceptingPlaces()) {
			final var predicate = getPlacePredicate(place);
			final var check = IncrementalPlicationChecker
					.convertLBool2Validity(SmtUtils.checkSatTerm(mScript, predicate.getFormula()));
			result = result.and(check);

			if (result == Validity.INVALID) {
				mLogger.warn("Annotation %s of error place %s is satisfiable", predicate, place);
				break;
			}
		}
		return result;
	}

	public Validity isValid() {
		return mIsInductive.and(mIsInterferenceFree).and(mIsProgramSafe);
	}
}
