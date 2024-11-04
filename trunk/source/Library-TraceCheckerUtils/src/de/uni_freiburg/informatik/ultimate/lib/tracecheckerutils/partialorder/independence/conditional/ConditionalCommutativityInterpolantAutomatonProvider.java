/*
 * Copyright (C) 2024 Marcel Ebbinghaus
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * Provides an interpolant automaton.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class ConditionalCommutativityInterpolantAutomatonProvider<L extends IAction> {
	private final Set<L> mAlphabet;
	private final IEmptyStackStateFactory<IPredicate> mFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	private NestedWordAutomaton<L, IPredicate> mAutomaton;

	private boolean mHasFalseBeforeEnd;

	/**
	 * Constructs a new instance of ConditionalCommutativityInterpolantAutomatonProvider.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param services
	 *            Ultimate services
	 * @param abstraction
	 *            Abstraction
	 * @param emptyStackStateFactory
	 *            Factory
	 * @param predicateUnifier
	 *            predicate unifier
	 */
	public ConditionalCommutativityInterpolantAutomatonProvider(final IUltimateServiceProvider services,
			final Set<L> alphabet, final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory,
			final IPredicateUnifier predicateUnifier) {
		mServices = services;
		mAlphabet = alphabet;
		mFactory = emptyStackStateFactory;
		mPredicateUnifier = predicateUnifier;
	}

	public static <L extends IAction> ConditionalCommutativityInterpolantAutomatonProvider<L> fromRefinementResult(
			final IUltimateServiceProvider services, final Set<L> alphabet,
			final IEmptyStackStateFactory<IPredicate> factory, final Word<L> word,
			final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> result) {
		final ConditionalCommutativityInterpolantAutomatonProvider<L> conComInterpolantProvider =
				new ConditionalCommutativityInterpolantAutomatonProvider<>(services, alphabet, factory,
						result.getPredicateUnifier());
		conComInterpolantProvider.setInterpolantAutomaton(null);
		for (final var tp : result.getInfeasibilityProof()) {
			conComInterpolantProvider.addToInterpolantAutomaton(tp.getTracePredicates(), word);
		}
		return conComInterpolantProvider;
	}

	/**
	 * Extends the interpolant automaton using a list of predicates and a word. Make sure predicates are a proof for the
	 * given word!
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param predicates
	 *            Predicates
	 * @param word
	 *            Word, i.e. a sequence of letters
	 * @return interpolant automaton
	 */
	public void addToInterpolantAutomaton(final TracePredicates tracePredicates, final Word<L> word) {
		final var precondition = mPredicateUnifier.getOrConstructPredicate(tracePredicates.getPrecondition());
		if (!mAutomaton.contains(precondition)) {
			mAutomaton.addState(true, false, precondition);
		}
		if (!mAutomaton.contains(mPredicateUnifier.getFalsePredicate())) {
			mAutomaton.addState(false, true, mPredicateUnifier.getFalsePredicate());
		}

		final var predicates = tracePredicates.getPredicates();
		for (int i = 0; i < predicates.size(); i++) {
			final IPredicate prePred = mPredicateUnifier
					.getOrConstructPredicate(i == 0 ? tracePredicates.getPrecondition() : predicates.get(i - 1));
			final IPredicate succPred = mPredicateUnifier.getOrConstructPredicate(predicates.get(i));
			if (!mAutomaton.contains(succPred)) {
				mAutomaton.addState(false, false, succPred);
			}
			mAutomaton.addInternalTransition(prePred, word.getSymbol(i), succPred);
		}

		final IPredicate prePred =
				predicates.isEmpty() ? tracePredicates.getPrecondition() : predicates.get(predicates.size() - 1);
		mHasFalseBeforeEnd |= SmtUtils.isFalseLiteral(prePred.getFormula());
	}

	/**
	 * Sets the interpolant automaton to the given interpolant automaton and constructs an empty automaton if null is
	 * given. Make sure that the given automaton is an interpolant automaton!
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param automaton
	 *            The given interpolant automaton
	 */
	public void setInterpolantAutomaton(final NestedWordAutomaton<L, IPredicate> automaton) {
		if (automaton != null) {
			mAutomaton = automaton;
		} else {
			final VpAlphabet<L> vpAlphabet = new VpAlphabet<>(mAlphabet);
			mAutomaton = new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), vpAlphabet, mFactory);
		}
	}

	/**
	 * Returns the interpolant automaton.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @return interpolant automaton
	 */
	public NestedWordAutomaton<L, IPredicate> getInterpolantAutomaton() {
		return mAutomaton;
	}

	public boolean hasFalseBeforeEnd() {
		return mHasFalseBeforeEnd;
	}
}
