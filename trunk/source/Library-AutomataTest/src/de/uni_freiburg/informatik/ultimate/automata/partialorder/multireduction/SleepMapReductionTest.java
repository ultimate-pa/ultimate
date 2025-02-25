/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Complement;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ConcurrentProduct;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Union;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AcceptingRunSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.AutomatonConstructingVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class SleepMapReductionTest {
	public SleepMapReductionTest() {
	}

	@Test
	public void testStratified() {
		final IUltimateServiceProvider services = UltimateMocks.createUltimateServiceProviderMock();
		final var mLogger = services.getLoggingService().getLogger(getClass());
		final var mServices = new AutomataLibraryServices(services);
		final var stateFactory = new StateFactory();

		final var order = new IDfsOrder<Character, String>() {
			@Override
			public Comparator<Character> getOrder(final String state) {
				return Comparator.naturalOrder();
			}

			@Override
			public boolean isPositional() {
				return false;
			}
		};

		final INestedWordAutomaton<Character, String> proof;
		final INestedWordAutomaton<Character, String> program;
		try {
			final var testWord = NestedWord.nestedWord(new Word<>('a', 'b', 'c', 'd'));

			final var A_ac = buildWordAutomaton(mServices, "ac");
			final var A_bd = buildWordAutomaton(mServices, "bd");
			program = new ConcurrentProduct<>(mServices, stateFactory, A_ac, A_bd, true).getResult();
			assert new Accepts<>(mServices, program, testWord).getResult() : "program rejects test word";

			final var A_abdc = buildWordAutomaton(mServices, "abdc");
			final var A_bacd = buildWordAutomaton(mServices, "bacd");
			proof = new Complement<>(mServices, stateFactory,
					new Union<>(mServices, stateFactory, A_abdc, A_bacd).getResult()).getResult();
			assert new Accepts<>(mServices, proof, testWord).getResult() : "proof rejects test word";

			final var product = new InformationStorage<>(program, proof, stateFactory, s -> false);
			assert new Accepts<>(mServices, product, testWord).getResult() : "product rejects test word";

			final var indep1Rel = new HashRelation<Character, Character>();
			indep1Rel.addPair('a', 'b');
			indep1Rel.addPair('b', 'a');
			final var indep1 = new HashIndependence(indep1Rel);

			final var indep2Rel = new HashRelation<Character, Character>();
			indep2Rel.addPair('c', 'd');
			indep2Rel.addPair('d', 'c');
			final var indep2 = new HashIndependence(indep2Rel);

			final Function<SleepMapReduction<Character, String, String>, IBudgetFunction<Character, String>> getBudget =
					smr -> new OptimisticBudget<>(mServices, order, stateFactory,
							() -> new AcceptingRunSearchVisitor<>(isAccepting(proof)), smr);

			final var smr = new SleepMapReduction<>(product, List.of(indep1, indep2), order, stateFactory, getBudget);

			assert !isAccepting(proof).test("(ac;bd)##<sink>::<sink>~{}~0") : "state is unexpectedly accepting";
			final var bv = new AutomatonConstructingVisitor<>(smr::isInitial, isAccepting(proof), smr.getVpAlphabet(),
					mServices, stateFactory);
			DepthFirstTraversal.traverse(mServices, smr, order, bv);
			mLogger.warn(bv.getReductionAutomaton());

			mLogger.warn("traversing reduction");
			final var visitor = new AcceptingRunSearchVisitor<Character, String>(isAccepting(proof));
			DepthFirstTraversal.traverse(mServices, smr, order, visitor);
			final var run = visitor.getAcceptingRun();
			assert run == null : "Found uncovered run: " + run.getStateSequence() + " for word " + run.getWord();

			mLogger.warn("Everything passed, run=" + run);

		} catch (final AutomataLibraryException e) {
			throw new RuntimeException(e);
		}
	}

	private Predicate<String> isAccepting(final INestedWordAutomaton<?, String> proof) {
		return s -> {
			final var split = s.split("##");
			final var programState = split[0];
			final var proofState = split[1].split("~")[0];
			final var proofAccepting = proof.getStates().stream().filter(proof::isFinal).toList();
			return programState.equals("(ac;bd)")
					&& !proof.getStates().stream().filter(proof::isFinal).anyMatch(proofState::equals);
		};
	}

	private INestedWordAutomaton<Character, String> buildWordAutomaton(final AutomataLibraryServices services,
			final String word) {
		final var alphabet = new VpAlphabet<>(word.chars().mapToObj(c -> (char) c).collect(Collectors.toSet()));

		final var A_abdc = new NestedWordAutomaton<Character, String>(services, alphabet, () -> null);
		String pred = null;
		for (int i = 0; i <= word.length(); ++i) {
			final var state = i == 0 ? "ε" : word.substring(0, i);
			A_abdc.addState(i == 0, i == word.length(), state);
			if (pred != null) {
				final var letter = word.charAt(i - 1);
				A_abdc.addInternalTransition(pred, letter, state);
			}
			pred = state;
		}
		return A_abdc;
	}

	private final static class HashIndependence implements IIndependenceRelation<String, Character> {
		private final HashRelation<Character, Character> mRelation;

		public HashIndependence(final HashRelation<Character, Character> relation) {
			mRelation = relation;
		}

		@Override
		public boolean isSymmetric() {
			return false;
		}

		@Override
		public boolean isConditional() {
			return false;
		}

		@Override
		public Dependence isIndependent(final String state, final Character a, final Character b) {
			return mRelation.containsPair(a, b) ? Dependence.INDEPENDENT : Dependence.DEPENDENT;
		}

		@Override
		public ISymbolicIndependenceRelation<Character, String> getSymbolicRelation() {
			return null;
		}
	}

	private final static class StateFactory implements IUnionStateFactory<String>, IDeterminizeStateFactory<String>,
			IConcurrentProductStateFactory<String>, IIntersectionStateFactory<String>,
			ISleepMapStateFactory<Character, String, String> {
		private final Map<String, String> mUnifier = new HashMap<>();
		private final Map<String, SleepMap<Character, String>> mMapStorage = new HashMap<>();

		@Override
		public String createEmptyStackState() {
			return "<empty>";
		}

		@Override
		public String createSinkStateContent() {
			return "<sink>";
		}

		@Override
		public String union(final String state1, final String state2) {
			return state1 + "::" + state2;
		}

		@Override
		public String determinize(final Map<String, Set<String>> down2up) {
			return down2up.toString();
		}

		@Override
		public String concurrentProduct(final String state1, final String state2) {
			return "(" + state1 + ";" + state2 + ")";
		}

		@Override
		public String intersection(final String state1, final String state2) {
			return state1 + "##" + state2;
		}

		@Override
		public String createSleepMapState(final String state, final SleepMap<Character, String> sleepMap,
				final int budget) {
			final String reprState = mUnifier.putIfAbsent(state, state);
			assert reprState == null || reprState == state;
			final String sleepMapState = "%s~%s~%d".formatted(state, sleepMap, budget);
			final var oldSleepMap = mMapStorage.putIfAbsent(sleepMapState, sleepMap);
			assert oldSleepMap == null || oldSleepMap.equals(sleepMap) : "";
			return sleepMapState;
		}

		@Override
		public String getOriginalState(final String sleepMapState) {
			final var reprState = mUnifier.get(sleepMapState.split("~")[0]);
			assert reprState != null;
			return reprState;
		}

		@Override
		public SleepMap<Character, String> getSleepMap(final String sleepMapState) {
			final var sleepMap = mMapStorage.get(sleepMapState);
			assert sleepMap != null;
			return sleepMap;
		}

		@Override
		public int getBudget(final String sleepMapState) {
			return Integer.parseInt(sleepMapState.split("~")[2]);
		}
	}
}
