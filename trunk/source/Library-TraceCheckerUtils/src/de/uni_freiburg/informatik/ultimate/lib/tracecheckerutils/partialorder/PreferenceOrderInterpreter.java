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
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.yaml.snakeyaml.Yaml;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.Dfs2PreferenceOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.IPreferenceOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.IfElsePreferenceOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.SequentialPreferenceOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
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
	private final IIcfg<?> mIcfg;
	private final Collection<? extends IcfgLocation> mErrorLocs;
	private final VpAlphabet<L> mAlphabet;

	public PreferenceOrderInterpreter(final IIcfg<?> icfg, final Collection<? extends IcfgLocation> errorLocs) {
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
		}
		if ("ifelse".equals(spec.get("operator"))) {
			return buildIfElseComposition(spec, left, right);
		}

		// TODO add support for other combination operators here

		throw new UnsupportedOperationException("Unknown type of preference order: " + spec);
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

		final var loopHeads = mIcfg.getLoopLocations();
		final Set<IcfgEdge> loopEdges =
				loopHeads.stream().flatMap(PreferenceOrderInterpreter::getLoopClosingEdges).collect(Collectors.toSet());

		return new ParameterizedPreferenceOrder<>(steps, threads, mAlphabet, loopEdges::contains);
	}

	private static Stream<IcfgEdge> getLoopClosingEdges(final IcfgLocation loopHead) {
		return new IcfgEdgeIterator(loopHead.getOutgoingEdges()).asStream()
				.filter(loopHead.getIncomingEdges()::contains);
	}

	private IPreferenceOrder<L, IPredicate, ?> buildSequentialCompositionOrder() {
		// FIXME code duplicated from PartialOrderReductionFacade
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
