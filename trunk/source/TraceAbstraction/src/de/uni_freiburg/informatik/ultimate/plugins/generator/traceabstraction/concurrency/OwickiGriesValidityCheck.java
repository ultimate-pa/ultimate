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

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
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

	private final boolean mIsInductive;
	private final boolean mIsInterferenceFree;
	private final OwickiGriesAnnotation<LETTER, PLACE> mAnnotation;
	private final Collection<ITransition<LETTER, PLACE>> mTransitions;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final BasicPredicateFactory mPredicateFactory;
	private final HashRelation<ITransition<LETTER, PLACE>, PLACE> mCoMarkedPlaces;

	public OwickiGriesValidityCheck(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final OwickiGriesAnnotation<LETTER, PLACE> annotation,
			final HashRelation<ITransition<LETTER, PLACE>, PLACE> coMarkedPlaces) {

		mServices = services;
		mLogger = services.getLoggingService().getLogger(OwickiGriesValidityCheck.class);
		mManagedScript = csToolkit.getManagedScript();
		mAnnotation = annotation;
		mPredicateFactory = new BasicPredicateFactory(services, mManagedScript, annotation.getSymbolTable());
		mCoMarkedPlaces = coMarkedPlaces;

		mHoareTripleChecker = new MonolithicHoareTripleChecker(csToolkit);
		mTransitions = mAnnotation.getPetriNet().getTransitions();

		mIsInductive = checkInductivity();
		mIsInterferenceFree = checkInterference(); // TODO
	}

	private boolean checkInductivity() {
		// TODO: check this line code
		for (final ITransition<LETTER, PLACE> transition : mTransitions) {
			if (!getTransitionInductivity(transition)) {
				return false;
			}
		}
		return true;
	}

	private boolean getTransitionInductivity(final ITransition<LETTER, PLACE> Transition) {
		final Set<PLACE> predecessors = mAnnotation.getPetriNet().getPredecessors(Transition);
		for (final PLACE pre : predecessors) {
			mLogger.info(getPlacePredicate(pre));
		}
		final IPredicate precondition = getConjunctionPredicate(predecessors);
		final IPredicate postcondition = getConjunctionPredicate(mAnnotation.getPetriNet().getSuccessors(Transition));
		return getValidityResult(
				mHoareTripleChecker.checkInternal(precondition, getTransitionSeqAction(Transition), postcondition));
	}

	private IPredicate getConjunctionPredicate(final Set<PLACE> set) {
		final Collection<IPredicate> predicates = new HashSet<>();
		set.stream().forEach(element -> predicates.add(getPlacePredicate(element)));
		return mPredicateFactory.and(predicates);
	}

	private IInternalAction getTransitionSeqAction(final ITransition<LETTER, PLACE> Transition) {
		final List<UnmodifiableTransFormula> actions = Arrays.asList(Transition.getSymbol().getTransformula(),
				mAnnotation.getAssignmentMapping().get(Transition));
		return new BasicInternalAction(null, null, TransFormulaUtils.sequentialComposition(mLogger, mServices,
				mManagedScript, false, false, false, null, null, actions));
	}

	private IPredicate getPlacePredicate(final PLACE Place) {
		return mAnnotation.getFormulaMapping().get(Place);
	}

	private boolean getValidityResult(final Validity validity) {
		final boolean result;
		if (validity == Validity.VALID) {
			result = true;
		} else {
			result = false;
		}
		return result;
	}

	private boolean checkInterference() {
		if (mTransitions.stream().filter(transition -> !getTransitionInterFree(transition)).count() >= 1) {
			return false;
		}
		return true;
	}

	private boolean getTransitionInterFree(final ITransition<LETTER, PLACE> Transition) {
		final IPredicate PredecessorsPred =
				getConjunctionPredicate(mAnnotation.getPetriNet().getPredecessors(Transition));
		final IInternalAction Action = getTransitionSeqAction(Transition);
		final Set<PLACE> Comarked = getComarkedPlaces(Transition);
		if (Comarked.stream().filter(place -> !getInterferenceFreeTriple(PredecessorsPred, Action, place))
				.count() >= 1) {
			return false;
		}
		return true;
	}

	private Set<PLACE> getComarkedPlaces(final ITransition<LETTER, PLACE> transition) {
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
		return getValidityResult(
				mHoareTripleChecker.checkInternal(mPredicateFactory.and(predicate), Action, placePred));
	}

	public boolean isValid() {
		return mIsInductive && mIsInterferenceFree;
	}
}
