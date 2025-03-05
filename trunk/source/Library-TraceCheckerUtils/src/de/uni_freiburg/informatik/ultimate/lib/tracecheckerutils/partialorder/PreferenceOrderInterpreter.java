/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.Dfs2PreferenceOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.IPreferenceOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.IfElsePreferenceOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.ProductPreferenceOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.SequentialPreferenceOrder;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton.Cfg2Automaton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Interprets specifications of preference orders, constructed from a few built-in orders and several combination
 * operators, and creates the corresponding {@link IPreferenceOrder}.
 *
 * @param <L>
 *            The type of letters
 */
public class PreferenceOrderInterpreter<L extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final IIcfg<?> mIcfg;
	private final Collection<? extends IcfgLocation> mErrorLocs;
	private final VpAlphabet<L> mAlphabet;

	public PreferenceOrderInterpreter(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final Collection<? extends IcfgLocation> errorLocs) {
		mServices = services;
		mIcfg = icfg;
		mErrorLocs = errorLocs;
		mAlphabet = Cfg2Automaton.extractVpAlphabet(icfg, true);
	}

	public IPreferenceOrder<L, IPredicate, ?> interpret(final String prefOrderSpec) {
		return interpret(new Yaml().<Map<String, Object>> load(prefOrderSpec));
	}

	private IPreferenceOrder<L, IPredicate, ?> interpret(final Map<String, Object> spec) {
		switch ((String) spec.get("builtin")) {
		case "loop_lockstep":
			return buildLoopLockstepOrder(spec);
		case "seq_comp":
			return buildSequentialCompositionOrder();
		case "empty":
			return buildEmptyOrder();
		case "checkpoint":
			return buildCheckpointOrder(spec);
		case "fixed_order":
			return buildFixedOrder(spec);
		// TODO add other builtin order types if needed
		case null:
			// handled below
			break;

		default:
			throw new UnsupportedOperationException("unknown type of builtin order: " + spec.get("builtin"));
		}

		assert spec.containsKey("operator") : "neither builtin order nor order combination operator: " + spec;

		final var left = interpret((Map<String, Object>) spec.get("left"));
		final var right = interpret((Map<String, Object>) spec.get("right"));

		if ("sequential".equals(spec.get("operator"))) {
			return buildSequentialComposition(spec, left, right);
		} else if ("ifelse".equals(spec.get("operator"))) {
			return buildIfElseComposition(spec, left, right);
		} else if ("product".equals(spec.get("operator"))) {
			return buildProductComposition(spec, left, right);
		}
		// TODO add support for other combination operators here

		throw new UnsupportedOperationException("Unknown type of preference order: " + spec);
	}

	private IPreferenceOrder<L, IPredicate, ?> buildFixedOrder(final Map<String, Object> spec) {

		final Object state = new Object();
		final var monitor = new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), mAlphabet, () -> null);
		monitor.addState(true, true, state);
		for (final var letter : mAlphabet.getInternalAlphabet()) {
			monitor.addInternalTransition(state, letter, state);
		}

		final Map<String, Integer> poMap = (Map<String, Integer>) spec.get("partial_order");
		return new FixedOrder<>(mServices, mAlphabet, new PartialOrderMapComparator<L>(poMap));
	}

	/**
	 * A comparator that allows specifying a partial order on actions by mapping their thread (i.e. procedure) names to
	 * integers. Two threads mapped to the same integer are incomparable or equal, otherwise the class compares the
	 * corresponding integers.
	 *
	 * NOTE: The map data structure is restrictive and does not allow for all partial orders; e.g. it cannot represent
	 * an order where a is incomparable with b and c, but b is less than c.
	 *
	 * TODO Find a better representation.
	 *
	 * @param <L>
	 *            The type of letters being compared.
	 */
	// We use a record to save on boilerplate code and hashCode/equals implementations.
	private record PartialOrderMapComparator<L extends IAction>(Map<String, Integer> poMap) implements Comparator<L> {
		@Override
		public int compare(final L a, final L b) {
			final Integer threadAPos = poMap.get(a.getPrecedingProcedure());
			final Integer threadBPos = poMap.get(b.getSucceedingProcedure());
			if (threadAPos == null || threadBPos == null) {
				// A thread that is not mentioned in the map is incomparable with all other threads.
				return 0;
			}
			return Integer.compare(threadAPos, threadBPos);
		}
	}

	// TODO This class overlaps with ConstantDfsOrder.
	// TODO Once we decide how to proceed with IDfsOrder vs IPreferenceOrder, eliminate one of them.
	// TODO Also, if we are sure that all users support getMonitor() == null, we can eliminate the dummy automaton.
	private static final class FixedOrder<L extends IAction> implements IPreferenceOrder<L, IPredicate, Object> {
		private final Comparator<L> mAlphabetOrder;
		private final NestedWordAutomaton<L, Object> mMonitor;

		public FixedOrder(final IUltimateServiceProvider services, final VpAlphabet<L> alphabet,
				final Comparator<L> alphabetOrder) {
			mAlphabetOrder = alphabetOrder;

			final Object state = new Object();
			mMonitor = new NestedWordAutomaton<>(new AutomataLibraryServices(services), alphabet, () -> null);
			mMonitor.addState(true, true, state);
			for (final var letter : alphabet.getInternalAlphabet()) {
				mMonitor.addInternalTransition(state, letter, state);
			}
		}

		@Override
		public Comparator<L> getOrder(final IPredicate programState, final Object monitorState) {
			return mAlphabetOrder;
		}

		@Override
		public boolean isPositional() {
			return false;
		}

		@Override
		public INwaOutgoingLetterAndTransitionProvider<L, Object> getMonitor() {
			return mMonitor;
		}
	}

	private IPreferenceOrder<L, IPredicate, ?> buildCheckpointOrder(final Map<String, Object> spec) {
		final var checkpoints = ((List<String>) spec.get("checkpoints")).stream().map(this::findLetter).toList();

		final var threads = checkpoints.stream().map(IAction::getPrecedingProcedure).toList();
		final var maxSteps = IntStream.range(0, threads.size()).mapToObj(i -> 1).toList();

		return new ParameterizedPreferenceOrder<>(maxSteps, threads, mAlphabet, checkpoints::contains);
	}

	// TODO add empty order
	private IPreferenceOrder<L, IPredicate, ?> buildEmptyOrder() {
		return null;
	}

	private IPreferenceOrder<L, IPredicate, ?> buildLoopLockstepOrder(final Map<String, Object> spec) {
		final List<String> threads = new ArrayList<>();
		final List<Integer> steps = new ArrayList<>();
		final var iterations = (List<List<Object>>) spec.get("iterations");
		for (final var pair : iterations) {
			threads.add((String) pair.get(0));
			steps.add((int) pair.get(1));
		}

		final Predicate<L> isLoopEdge = (Predicate) ParameterizedPreferenceOrderUtils.getLoopClosingEdges(mIcfg);
		return new ParameterizedPreferenceOrder<>(steps, threads, mAlphabet, isLoopEdge);
	}

	private IPreferenceOrder<L, IPredicate, ?> buildSequentialCompositionOrder() {
		// FIXME code duplicated from PartialOrderReductionFacade
		// Monitor sequential composition is defined below, this is different!
		final Set<String> errorThreads =
				mErrorLocs.stream().map(IcfgLocation::getProcedure).collect(Collectors.toSet());
		return new Dfs2PreferenceOrder<>(new ConstantDfsOrder<>(
				Comparator.<L, Boolean> comparing(x -> !errorThreads.contains(x.getPrecedingProcedure()))
						.thenComparing(Comparator.comparing(
								(Function<? super L, ? extends String>) IIcfgTransition::getPrecedingProcedure))
						.thenComparing(Comparator.comparingInt(Object::hashCode))));
	}

	private <S1, S2> IPreferenceOrder<L, IPredicate, ?> buildSequentialComposition(final Map<String, Object> spec,
			final IPreferenceOrder<L, IPredicate, S1> left, final IPreferenceOrder<L, IPredicate, S2> right) {
		final Set<L> letters =
				((List<String>) spec.get("switch_on")).stream().map(this::findLetter).collect(Collectors.toSet());

		return SequentialPreferenceOrder.create(left, right, ImmutableSet.of(letters));
	}

	private <S1, S2> IPreferenceOrder<L, IPredicate, ?> buildIfElseComposition(final Map<String, Object> spec,
			final IPreferenceOrder<L, IPredicate, S1> left, final IPreferenceOrder<L, IPredicate, S2> right) {
		final Set<L> letters =
				((List<String>) spec.get("switch_on")).stream().map(this::findLetter).collect(Collectors.toSet());

		return IfElsePreferenceOrder.create(left, right, ImmutableSet.of(letters));
	}

	private <S1, S2> IPreferenceOrder<L, IPredicate, ?> buildProductComposition(final Map<String, Object> spec,
			final IPreferenceOrder<L, IPredicate, S1> left, final IPreferenceOrder<L, IPredicate, S2> right) {

		return ProductPreferenceOrder.create(left, right);
	}

	private L findLetter(final String description) {
		final var matchingLetters = mAlphabet.getInternalAlphabet().stream()
				.filter(l -> l.toString().startsWith(description)).collect(Collectors.toList());
		if (matchingLetters.isEmpty()) {
			throw new IllegalArgumentException("Did not find any letter matching '" + description + "'");
		}
		if (matchingLetters.size() > 1) {
			throw new IllegalArgumentException("Description '" + description + "' is ambiguous: found "
					+ matchingLetters.size() + " matching letters");
		}
		return matchingLetters.get(0);
	}
}
