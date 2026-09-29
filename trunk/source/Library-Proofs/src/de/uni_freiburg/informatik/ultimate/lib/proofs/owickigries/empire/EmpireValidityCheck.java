/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class EmpireValidityCheck<L extends IAction, P, S> {
	private final ILogger mLogger;

	private final MonolithicHoareTripleChecker mHc;
	private final BasicPredicateFactory mFactory;

	private final IEmpire<L, P, S> mEmpire;
	private final IPetriNet<L, P> mNet;
	private final Validity mValidity;

	public EmpireValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final BasicPredicateFactory factory, final IPetriNet<L, P> net,
			final ModifiableGlobalsTable modifiableGlobals, final IEmpire<L, P, S> empire) {
		mLogger = services.getLoggingService().getLogger(EmpireValidityCheck.class);
		mHc = new MonolithicHoareTripleChecker(mgdScript, modifiableGlobals);
		mFactory = factory;

		mNet = net;
		mEmpire = empire;

		mValidity = checkValidity();
	}

	private Validity checkValidity() {
		final var initialStates = mEmpire.getInitialStates();
		final Set<S> initialState = new HashSet<>();
		initialStates.forEach(initialState::add);

		if (checkInitialTerritories(initialState) != Validity.VALID) {
			return Validity.INVALID;
		}

		final var successorValidity = checkSuccessorValidity(initialState);
		if (successorValidity.getFirst() != Validity.VALID) {
			return Validity.INVALID;
		}

		if (checkAcceptingPlaces(successorValidity.getSecond()) != Validity.VALID) {
			return Validity.INVALID;
		}

		return Validity.VALID;
	}

	private Validity checkInitialTerritories(final Set<S> initialState) {
		if (initialState.isEmpty()) {
			mLogger.warn("Empire annotation does not contain any initial Territory");
			return Validity.INVALID;
		}
		for (final S state : initialState) {
			final var territory = mEmpire.getTerritory(state);
			if (!territory.containsMarking(Marking.initial(mNet))) {
				mLogger.warn("Initial State does not contain initial marking: %s", state);
				return Validity.INVALID;
			}
			final var law = mEmpire.getLaw(state);
			if (!isTrueLiteral(law)) {
				mLogger.warn("Initial State contains Law that does not evaluate to true: %s", state);
				return Validity.INVALID;
			}
		}
		return Validity.VALID;
	}

	private Pair<Validity, Set<S>> checkSuccessorValidity(final Set<S> initialState) {
		final Set<S> visitedStates = new HashSet<>();
		final var queue = new ArrayDeque<S>();
		for (final S state : initialState) {
			queue.offer(state);
		}
		while (!queue.isEmpty()) {
			final var state = queue.poll();
			if (!visitedStates.add(state)) {
				continue;
			}
			final var territory = mEmpire.getTerritory(state);
			final var law = mEmpire.getLaw(state);
			for (final var transition : (Iterable<Transition<L, P>>) territory.getEnabledTransitions(mNet)::iterator) {
				final var successorStates = mEmpire.internalSuccessors(state, transition);
				final Set<S> successorState = new HashSet<>();
				successorStates.forEach(i -> successorState.add(i.getSucc()));
				assert successorState.size() < 2 : "More then one successor";
				final Validity contradiction = checkContradiction(law, transition);
				if (contradiction != Validity.VALID && successorState.isEmpty()) {
					mLogger.warn("The State:\n \t%s \n \thas no valid successor and does not evaluate to false with \n "
							+ "\ttransition %s", state, transition.getSymbol().getTransformula());
					return new Pair<>(Validity.INVALID, Collections.emptySet());
				}
				final var hoareValidity = checkHoareValidity(successorState, law, transition);
				if (!hoareValidity) {
					return new Pair<>(Validity.INVALID, Collections.emptySet());
				}
				final var isValidSuccessor = checkValidSuccessor(successorState, state, transition);
				if (!isValidSuccessor) {
					return new Pair<>(Validity.INVALID, Collections.emptySet());
				}
				for (final var succ : successorState) {
					queue.offer(succ);
				}
			}
		}
		return new Pair<>(Validity.VALID, visitedStates);
	}

	private Validity checkAcceptingPlaces(final Set<S> states) {
		final var accepting = mNet.getAcceptingPlaces();
		for (final S state : states) {
			final var territory = mEmpire.getTerritory(state);
			final var law = mEmpire.getLaw(state);
			if (DataStructureUtils.haveNonEmptyIntersection(territory.getPlaces(), accepting) && !isFalseLiteral(law)) {
				return Validity.INVALID;
			}
		}
		return Validity.VALID;
	}

	private boolean checkHoareTriple(final IPredicate pre, final IPredicate post, final Transition<L, P> transition) {
		final IPredicate flattenedPre = mFactory.and(PredicateWithConjuncts.flatten(pre));
		final IPredicate flattenedPost = mFactory.and(PredicateWithConjuncts.flatten(post));
		final var valid = mHc.checkInternal(flattenedPre, (IInternalAction) transition.getSymbol(), flattenedPost);
		return valid == Validity.VALID;
	}

	private Validity checkContradiction(final IPredicate lawConjunction, final Transition<L, P> transition) {
		if (!checkHoareTriple(lawConjunction, mFactory.or(), transition)) {
			return Validity.INVALID;
		}
		return Validity.VALID;
	}

	private boolean checkHoareValidity(final Set<S> successorState, final IPredicate law,
			final Transition<L, P> transition) {
		for (final S state : successorState) {
			final var successorLaw = mEmpire.getLaw(state);
			final var valid = checkHoareTriple(law, successorLaw, transition);
			if (!valid) {
				mLogger.warn("Invalid Hoare Triple\n \tprecondition %s \taction %s \tpostcondition %s", law,
						transition.getSymbol().getTransformula(), successorLaw);
				return false;
			}
		}
		return true;
	}

	private boolean checkValidSuccessor(final Set<S> successorState, final S predState,
			final Transition<L, P> transition) {
		final var territory = mEmpire.getTerritory(predState);
		for (final S state : successorState) {
			if (!territory.isSuccessor(mEmpire.getTerritory(state), transition)) {
				return false;
			}
		}
		return true;
	}

	public Validity getValidity() {
		return mValidity;
	}

	private boolean isFalseLiteral(final IPredicate predicate) {
		if (predicate instanceof final PredicateWithConjuncts conjunction) {
			return conjunction.getConjuncts().stream().anyMatch(this::isFalseLiteral);
		}
		return SmtUtils.isFalseLiteral(predicate.getFormula());
	}

	private boolean isTrueLiteral(final IPredicate predicate) {
		if (predicate instanceof final PredicateWithConjuncts conjunction) {
			return conjunction.getConjuncts().stream().allMatch(this::isTrueLiteral);
		}
		return SmtUtils.isTrueLiteral(predicate.getFormula());
	}
}
