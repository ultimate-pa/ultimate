/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Contains some methods useful to debug problems with {@link PartialOrderCegarLoop}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public final class PartialOrderUtil {
	private PartialOrderUtil() {
	}

	public static <L> Word<L> makeWord(final Class<L> clazz, final Set<L> alphabet, final int... hashes) {
		return NestedWord.nestedWord(new Word<>(
				Arrays.stream(hashes).mapToObj(hs -> alphabet.stream().filter(l -> l.hashCode() == hs).findAny().get())
						.toArray(i -> (L[]) Array.newInstance(clazz, i))));
	}

	public static <L> String printWordHashes(final Word<L> word) {
		return "{ " + word.asList().stream().mapToInt(Object::hashCode).mapToObj(Integer::toString)
				.collect(Collectors.joining(", ")) + " }";
	}

	// Useful for debugging. Not optimized at all, might only work in limited cases.
	public static <L, S> Word<L> computeRepresentative(final Word<L> word, final Class<L> clazz,
			final INwaOutgoingLetterAndTransitionProvider<L, S> automaton,
			final IIndependenceRelation<S, L> independence, final IDfsOrder<L, S> order) {
		final List<L> pref = new ArrayList<>(word.length());
		final List<L> suff = new ArrayList<>(word.asList());
		S state = automaton.getInitialStates().iterator().next();
		while (!suff.isEmpty()) {
			final List<OutgoingInternalTransition<L, S>> worklist = new ArrayList<>();
			automaton.internalSuccessors(state).forEach(worklist::add);
			worklist.sort(Comparator.comparing(OutgoingInternalTransition::getLetter, order.getOrder(state)));
			final int sizeBefore = suff.size();
			for (final OutgoingInternalTransition<L, S> t : worklist) {
				final L x = t.getLetter();
				final int index = suff.indexOf(x);
				if (index == -1) {
					continue;
				}
				boolean isNext = true;
				for (int i = 0; i < index; ++i) {
					if (independence.isIndependent(null, suff.get(i), x) != Dependence.INDEPENDENT) {
						isNext = false;
						break;
					}
				}
				if (!isNext) {
					continue;
				}
				pref.add(x);
				suff.remove(index);
				state = t.getSucc();
				break;
			}
			assert suff.size() == sizeBefore - 1 : "size must decrease in every iteration";
		}

		return new Word<>(pref.toArray(i -> (L[]) Array.newInstance(clazz, i)));
	}

	/**
	 * For debug usage in PartialOrderCegarLoop::isAbstractionEmpty.
	 *
	 * When some configuration declares a program safe, but a feasible counterexample is known (typically through
	 * #printWordHashes from another working configuration), this can be used to track at which iteration we lose the
	 * representative for this ctex.
	 *
	 * Call switchToOnDemandConstructionMode() before, and switchToReadonlyMode() after this method.
	 *
	 * Does not currently support conditional independence (#computeRepresentative needs to be adjusted).
	 *
	 * @param <L>
	 * @param services
	 * @param logger
	 * @param clazz
	 *            pass mTransitionClazz
	 * @param por
	 *            pass mPOR
	 * @param abstraction
	 *            pass mAbstraction
	 * @param isAccepting
	 *            pass PartialOrderCegarLoop::isGoalState
	 * @param hashes
	 *            array of letter hash codes for a feasible counterexample, as output by {@link #printWordHashes(Word)}
	 * @throws AutomataOperationCanceledException
	 */
	public static <L extends IIcfgTransition<?>> void checkFeasibleCounterexample(
			final IUltimateServiceProvider services, final ILogger logger, final Class<L> clazz,
			final PartialOrderReductionFacade<L, ?> por,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final Predicate<IPredicate> isAccepting, final int[] hashes) throws AutomataOperationCanceledException {
		logger.warn("computing representative of feasible ctex");
		final Word<L> feasCtex = makeWord(clazz, abstraction.getAlphabet(), hashes);
		final Word<L> repr =
				computeRepresentative(feasCtex, clazz, abstraction, por.getIndependence(0), por.getDfsOrder());
		logger.warn("Representative of feasible ctex is: " + PartialOrderUtil.printWordHashes(repr));

		logger.warn("building reduced automaton");
		final NestedWordAutomaton<L, IPredicate> reduced = por.constructReduction(abstraction, isAccepting);

		final boolean reprAccepted = accepts(services, reduced, repr);
		if (reprAccepted) {
			logger.warn("Representative of feasible ctex is accepted");
		}
		assert reprAccepted : "lost feas ctex";
	}

	private static <L> boolean accepts(final IUltimateServiceProvider services,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> nia, final Word<L> word)
			throws AutomataOperationCanceledException {
		try {
			return new Accepts<>(new AutomataLibraryServices(services), nia, NestedWord.nestedWord(word), false, false)
					.getResult();
		} catch (final AutomataOperationCanceledException e) {
			throw e;
		} catch (final AutomataLibraryException e) {
			throw new AssertionError(e);
		}
	}
}
