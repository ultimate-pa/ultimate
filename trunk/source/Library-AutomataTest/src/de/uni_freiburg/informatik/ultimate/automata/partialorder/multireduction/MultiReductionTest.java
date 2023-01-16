/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction;

import java.util.Set;

import org.junit.Before;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class MultiReductionTest {
	private AutomataLibraryServices mServices;

	@Before
	public void setUp() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		mServices = new AutomataLibraryServices(services);
	}

	private NestedWordAutomaton<Character, String> makeLinearAutomaton() {
		final var result = new NestedWordAutomaton<Character, String>(mServices,
				new VpAlphabet<>(Set.of('a', 'b', 'c')), () -> null);

		result.addState(true, false, "");
		result.addState(false, false, "a");
		result.addState(false, false, "ab");
		result.addState(false, true, "abc");
		result.addInternalTransition("", 'a', "a");
		result.addInternalTransition("a", 'b', "ab");
		result.addInternalTransition("ab", 'c', "abc");

		return result;
	}

	// @Test
	// public void test01() throws AutomataOperationCanceledException {
	// final SimpleDeadEndStore<Triple<String, SleepMap<Character, String>, Integer>> store =
	// new SimpleDeadEndStore<>();
	//
	// final var operand = makeLinearAutomaton();
	// final IIndependenceRelation<String, Character> full = fullIndependence();
	// final IDfsOrder<Character, Triple<String, SleepMap<Character, String>, Integer>> order = naturalOrder();
	// final ISleepMapStateFactory<Character, String, Triple<String, SleepMap<Character, String>, Integer>> factory =
	// tripleFactory();
	// final OptimisticBudget<Character, String, Triple<String, SleepMap<Character, String>, Integer>> budget =
	// new OptimisticBudget<>(mServices, order, factory,
	// () -> MultiReductionTest.searchVisitor(factory, "abc", store));
	// final var reduction = new SleepMapReduction<>(operand, List.of(full, full), order, factory, budget);
	// budget.setReduction(reduction);
	// DepthFirstTraversal.traverse(mServices, reduction, order, searchVisitor(factory, "abc", store));
	// }
	//
	// private static <L, S, R> IDfsVisitor<L, R> searchVisitor(final ISleepMapStateFactory<L, S, R> factory,
	// final S target, final SimpleDeadEndStore<R> store) {
	// return new DeadEndOptimizingSearchVisitor<>(
	// new AcceptingRunSearchVisitor<>(x -> target.equals(factory.getOriginalState(x)), null), store, false);
	// }
	//
	// private static <L, S> IIndependenceRelation<S, L> fullIndependence() {
	// return new IIndependenceRelation<>() {
	// @Override
	// public boolean isSymmetric() {
	// return true;
	// }
	//
	// @Override
	// public boolean isConditional() {
	// return false;
	// }
	//
	// @Override
	// public boolean contains(final S state, final L a, final L b) {
	// return true;
	// }
	// };
	// }
	//
	// private static <L extends Comparable<L>, S> IDfsOrder<L, S> naturalOrder() {
	// return new IDfsOrder<>() {
	// @Override
	// public boolean isPositional() {
	// return false;
	// }
	//
	// @Override
	// public Comparator<L> getOrder(final S state) {
	// return Comparator.naturalOrder();
	// }
	// };
	// }
	//
	// private static <L, S> ISleepMapStateFactory<L, S, Triple<S, SleepMap<L, S>, Integer>> tripleFactory() {
	// return new ISleepMapStateFactory<>() {
	//
	// @Override
	// public Triple<S, SleepMap<L, S>, Integer> createEmptyStackState() {
	// return null;
	// }
	//
	// @Override
	// public SleepMap<L, S> getSleepMap(final Triple<S, SleepMap<L, S>, Integer> sleepMapState) {
	// return sleepMapState.getSecond();
	// }
	//
	// @Override
	// public S getOriginalState(final Triple<S, SleepMap<L, S>, Integer> sleepMapState) {
	// return sleepMapState.getFirst();
	// }
	//
	// @Override
	// public int getBudget(final Triple<S, SleepMap<L, S>, Integer> sleepMapState) {
	// return sleepMapState.getThird();
	// }
	//
	// @Override
	// public Triple<S, SleepMap<L, S>, Integer> createSleepMapState(final S state, final SleepMap<L, S> sleepMap,
	// final int budget) {
	// return new Triple<>(state, sleepMap, budget);
	// }
	// };
	// }
}
