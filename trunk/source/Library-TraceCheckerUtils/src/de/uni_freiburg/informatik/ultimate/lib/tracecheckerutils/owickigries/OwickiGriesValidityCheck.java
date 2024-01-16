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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
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

/**
 * TODO
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <L>
 * @param <P>
 */
public class OwickiGriesValidityCheck<L extends IAction, P> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final Script mScript;

	private final Validity mIsInductive;
	private final Validity mIsInterferenceFree;
	private final Validity mIsProgramSafe;

	private final OwickiGriesAnnotation<L, P> mAnnotation;
	private final Collection<Transition<L, P>> mTransitions;
	private final Collection<P> mPlaces;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final BasicPredicateFactory mPredicateFactory;
	private final IPossibleInterferences<Transition<L, P>, P> mPossibleInterferences;

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final OwickiGriesAnnotation<L, P> annotation,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		this(services, csToolkit.getManagedScript(), new MonolithicHoareTripleChecker(csToolkit), annotation,
				possibleInterferences);
	}

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final ModifiableGlobalsTable modifiableGlobals, final OwickiGriesAnnotation<L, P> annotation,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		this(services, mgdScript, new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals), annotation,
				possibleInterferences);
	}

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker htc, final OwickiGriesAnnotation<L, P> annotation,
			final IPossibleInterferences<Transition<L, P>, P> possibleInterferences) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(OwickiGriesValidityCheck.class);
		mManagedScript = mgdScript;
		mScript = mgdScript.getScript();
		mAnnotation = annotation;
		mPredicateFactory = new BasicPredicateFactory(services, mManagedScript, annotation.getSymbolTable());
		mPossibleInterferences = possibleInterferences;

		mHoareTripleChecker = htc;
		mTransitions = mAnnotation.getPetriNet().getTransitions();
		mPlaces = mAnnotation.getPetriNet().getPlaces();

		mIsInductive = checkInductivity();
		mIsInterferenceFree = checkNonInterference();
		mIsProgramSafe = checkSafety();
	}

	private Validity checkInductivity() {
		Validity result = Validity.VALID;
		for (final Transition<L, P> transition : mTransitions) {
			final var check = isInductive(transition);
			result = result.and(check);

			if (result == Validity.INVALID) {
				break;
			}
		}
		return result;
	}

	private Validity isInductive(final Transition<L, P> transition) {
		final var precondition = getPrecondition(transition);
		final var postcondition = getPostcondition(transition);
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

		for (final P place : mPlaces) {
			final var check = isInterferenceFree(place);
			result = result.and(check);

			if (result == Validity.INVALID) {
				break;
			}
		}

		return result;
	}

	private Validity isInterferenceFree(final P place) {
		Validity result = Validity.VALID;

		for (final Transition<L, P> transition : mPossibleInterferences.getInterferingActions(place)) {
			final var check = isInterferenceFreeForTransition(place, transition);
			result = result.and(check);

			if (result == Validity.INVALID) {
				break;
			}
		}

		return result;
	}

	private Validity isInterferenceFreeForTransition(final P place, final Transition<L, P> transition) {
		final var annotation = getPlacePredicate(place);
		final var precondition = getPrecondition(transition);
		final var conjunction = Arrays.asList(precondition, annotation);
		final var action = getTransitionSeqAction(transition);

		final var result = mHoareTripleChecker.checkInternal(mPredicateFactory.and(conjunction), action, annotation);
		if (result == Validity.INVALID) {
			mLogger.warn(
					"Annotation %s of place %s is not interference-free under transition %s. Invalid Hoare triple:\n"
							+ "\tprecondition %s\n\ttransition %s\n\tpostcondition %s",
					annotation, place, transition, place, precondition, action, conjunction);
		}

		return result;
	}

	// TODO possibly cache?
	private IPredicate getPrecondition(final Transition<L, P> transition) {
		return mPredicateFactory
				.and(transition.getPredecessors().stream().map(this::getPlacePredicate).collect(Collectors.toSet()));
	}

	// TODO possibly cache?
	private IPredicate getPostcondition(final Transition<L, P> transition) {
		return mPredicateFactory
				.and(transition.getSuccessors().stream().map(this::getPlacePredicate).collect(Collectors.toSet()));
	}

	private IPredicate getPlacePredicate(final P place) {
		return mAnnotation.getFormulaMapping().get(place);
	}

	// TODO possibly cache?
	private IInternalAction getTransitionSeqAction(final Transition<L, P> transition) {
		final var transitionTf = transition.getSymbol().getTransformula();
		UnmodifiableTransFormula combinedTf;

		final var ghostUpdate = mAnnotation.getAssignmentMapping().get(transition);
		if (ghostUpdate == null) {
			combinedTf = transitionTf;
		} else {
			final var ghostTransition = ghostUpdate.makeTransitionFormula(mManagedScript, mAnnotation.getSymbolTable());
			combinedTf = TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, false, false,
					false, null, null, Arrays.asList(transitionTf, ghostTransition));
		}

		return new BasicInternalAction(null, null, combinedTf);
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
		for (final P place : mAnnotation.getPetriNet().getInitialPlaces()) {
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
		for (final P place : mAnnotation.getPetriNet().getAcceptingPlaces()) {
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
