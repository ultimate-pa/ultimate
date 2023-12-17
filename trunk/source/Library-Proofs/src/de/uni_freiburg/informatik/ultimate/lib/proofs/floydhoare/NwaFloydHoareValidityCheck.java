/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class NwaFloydHoareValidityCheck<L extends IAction, S> extends FloydHoareValidityCheck<S> {
	private final INestedWordAutomaton<L, S> mAutomaton;

	public NwaFloydHoareValidityCheck(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker hoareTripleChecker, final INestedWordAutomaton<L, S> automaton,
			final IFloydHoareAnnotation<S> annotation, final boolean assertValidity,
			final MissingAnnotationBehaviour missingAnnotations, final boolean checkSafety) {
		super(services, mgdScript, hoareTripleChecker, annotation, assertValidity, missingAnnotations, checkSafety);
		mAutomaton = automaton;

		mLogger.info("Starting Floyd-Hoare check of an automaton with " + automaton.sizeInformation());
		performCheck();
	}

	public static <L extends IAction> NwaFloydHoareValidityCheck<L, IPredicate> forInterpolantAutomaton(
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IHoareTripleChecker hoareTripleChecker, final IPredicateUnifier unifier,
			final INestedWordAutomaton<L, IPredicate> automaton, final boolean assertValidity) {
		return new NwaFloydHoareValidityCheck<>(services, mgdScript, hoareTripleChecker, automaton,
				new FloydHoareForInterpolantAutomaton(unifier), assertValidity, MissingAnnotationBehaviour.THROW,
				false);
	}

	@Override
	protected Iterable<S> getInitialStates() {
		return mAutomaton.getInitialStates();
	}

	@Override
	protected boolean isPostState(final S state) {
		return mAutomaton.isFinal(state);
	}

	@Override
	protected Iterable<Pair<IInternalAction, S>> getInternalSuccessors(final S state) {
		return successors(mAutomaton.internalSuccessors(state), IInternalAction.class);
	}

	@Override
	protected Iterable<Pair<ICallAction, S>> getCallSuccessors(final S state) {
		return successors(mAutomaton.callSuccessors(state), ICallAction.class);
	}

	@Override
	protected Iterable<Triple<IReturnAction, S, S>> getReturnSuccessors(final S state) {
		final var retSuccs = mAutomaton.returnSuccessors(state);
		return () -> new TransformIterator<>(retSuccs.iterator(),
				t -> new Triple<>((IReturnAction) t.getLetter(), t.getSucc(), t.getHierPred()));
	}

	private <A> Iterable<Pair<A, S>> successors(final Iterable<? extends IOutgoingTransitionlet<L, S>> successors,
			final Class<A> clazz) {
		return () -> new TransformIterator<>(successors.iterator(),
				t -> new Pair<>(clazz.cast(t.getLetter()), t.getSucc()));
	}
}