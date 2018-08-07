/*
 * Copyright (C) 2010-2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.statefactory;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.StateWithRankInfo;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.incrementalinclusion.IIncrementalInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationCheckResultStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetAndAutomataInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A {@link IStateFactory} for {@link String}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class StringFactory implements ISenwaStateFactory<String>, IBlackWhiteStateFactory<String>,
		IFinitePrefix2PetriNetStateFactory<String>, IBuchiComplementDeterministicStateFactory<String>,
		IBuchiComplementNcsbStateFactory<String>, IBuchiComplementSvwStateFactory<String>,
		IPetriNet2FiniteAutomatonStateFactory<String>, IIncrementalInclusionStateFactory<String>,
		IMinimizationStateFactory<String>, IMinimizationCheckResultStateFactory<String>, IUnionStateFactory<String>,
		IBuchiComplementNcsbSimpleStateFactory<String>, IRelabelStateFactory<String>,
		IConcurrentProductStateFactory<String>, IPetriNetAndAutomataInclusionStateFactory<String> {

	public static final String INFINITY = "∞";
	private static final String EMPTY_STRING = "";
	private static final String EMPTY_SET = "{}";
	private static final char X_STRING = 'X';
	private static final String COMMA_SPACE = ", ";
	private static final char COMMA = ',';
	private static final char OPEN_PARENTHESIS = '(';
	private static final char CLOSE_PARENTHESIS = ')';
	private static final char OPEN_BRACE = '{';
	private static final char CLOSE_BRACE = '}';
	private static final char OPEN_BRACKET = '[';
	private static final char CLOSE_BRACKET = ']';

	private static final int RANK_ONE = 1;
	private static final int RANK_TWO = 2;
	private static final int RANK_THREE = 3;
	private static final int MINIMUM_LIST_SIZE = 2;
	private static final int MINIMUM_PAIR_LIST_SIZE = 7;

	private String product(final String state1, final String state2) {
		final StringBuilder builder = new StringBuilder();
		// @formatter:off
		builder.append(OPEN_BRACKET)
				.append(state1)
				.append(COMMA_SPACE)
				.append(state2)
				.append(CLOSE_BRACKET);
		// @formatter:on
		return builder.toString();
	}

	@Override
	public String union(final String state1, final String state2) {
		// use the same string as for intersection
		return product(state1, state2);
	}

	@Override
	public String intersection(final String state1, final String state2) {
		return product(state1, state2);
	}

	@Override
	public String concurrentProduct(final String state1, final String state2) {
		return product(state1, state2);
	}

	@Override
	public String intersectBuchi(final String state1, final String state2, final int track) {
		final StringBuilder builder = new StringBuilder();
		// @formatter:off
		builder.append(OPEN_BRACKET)
				.append(state1)
				.append(COMMA_SPACE)
				.append(state2)
				.append(", track")
				.append(track)
				.append(CLOSE_BRACKET);
		// @formatter:on
		return builder.toString();
	}

	@Override
	public String determinize(final Map<String, Set<String>> down2up) {
		final StringBuilder builder = new StringBuilder(down2up.size() * MINIMUM_PAIR_LIST_SIZE);
		builder.append(OPEN_BRACE);
		for (final Entry<String, Set<String>> entry : down2up.entrySet()) {
			final String downState = entry.getKey();
			final Iterator<String> iterator = entry.getValue().iterator();
			String separator = EMPTY_STRING;
			while (iterator.hasNext()) {
				final String upState = iterator.next();
				// @formatter:off
				builder.append(separator)
						.append(OPEN_PARENTHESIS)
						.append(downState)
						.append(COMMA)
						.append(upState)
						.append(CLOSE_PARENTHESIS);
				// @formatter:on
				separator = COMMA_SPACE;
			}
		}
		builder.append(CLOSE_BRACE);
		return builder.toString();
	}

	@Override
	public String createSinkStateContent() {
		return "∅SinkState";
	}

	@Override
	public String createEmptyStackState() {
		return "€";
	}

	/*
	 * @Override public String getContentOnPetriNet2FiniteAutomaton(Collection<String> cList) { StringBuilder sb = new
	 * StringBuilder(); sb.append(OPEN_BRACE); boolean firstElement = true; for (String content :cList) { if
	 * (firstElement) { firstElement = false; } else { sb.append(","); } sb.append(content); } sb.append(CLOSE_BRACE);
	 * return sb.toString(); }
	 */

	@Override
	public String getContentOnPetriNet2FiniteAutomaton(final Marking<?, String> marking) {
		final StringBuilder builder = new StringBuilder(marking.size() * MINIMUM_LIST_SIZE);
		builder.append(OPEN_BRACE);
		boolean firstElement = true;
		for (final String place : marking) {
			if (firstElement) {
				firstElement = false;
			} else {
				builder.append(COMMA);
			}
			builder.append(place);
		}
		builder.append(CLOSE_BRACE);
		return builder.toString();
	}

	@Override
	public String getBlackContent(final String content) {
		return "Black:" + content;
	}

	@Override
	public String getWhiteContent(final String content) {
		return "White:" + content;
	}

	@Override
	public String buchiComplementFkv(final LevelRankingState<?, String> complementState) {
		if (complementState.isNonAcceptingSink()) {
			return complementState.toString();
		}

		final boolean isNestedWordAutomaton = !complementState.getOperand().getVpAlphabet().getCallAlphabet().isEmpty();
		final StringBuilder builder = new StringBuilder();
		builder.append(OPEN_BRACE);
		for (final StateWithRankInfo<String> downState : complementState.getDownStates()) {
			for (final StateWithRankInfo<String> upState : complementState.getUpStates(downState)) {
				builder.append(OPEN_PARENTHESIS);
				if (isNestedWordAutomaton) {
					buchiComplementFkvHelper(builder, downState);
					builder.append(COMMA);
				}
				buchiComplementFkvHelper(builder, upState);
				builder.append(CLOSE_PARENTHESIS);
			}
		}
		builder.append(CLOSE_BRACE);
		return builder.toString();
	}

	@Override
	public String buchiComplementNcsb(final LevelRankingState<?, String> complementState) {
		if (complementState.isNonAcceptingSink()) {
			return complementState.toString();
		}

		final List<Pair<StateWithRankInfo<String>, String>> listN = new ArrayList<>();
		final List<Pair<StateWithRankInfo<String>, String>> listC = new ArrayList<>();
		final List<Pair<StateWithRankInfo<String>, String>> listS = new ArrayList<>();
		final List<Pair<StateWithRankInfo<String>, String>> listB = new ArrayList<>();

		for (final StateWithRankInfo<String> downState : complementState.getDownStates()) {
			for (final StateWithRankInfo<String> upState : complementState.getUpStates(downState)) {
				if (!upState.hasRank()) {
					throw new IllegalArgumentException("must have rank");
				}
				switch (upState.getRank()) {
					case RANK_THREE:
						listN.add(new Pair<>(downState, upState.getState()));
						break;
					case RANK_TWO:
						buchiComplementNcsbHelperRankTwo(listC, listB, downState, upState);
						break;
					case RANK_ONE:
						listS.add(new Pair<>(downState, upState.getState()));
						break;
					default:
						throw new IllegalArgumentException("Only ranks 1, 2, 3 are allowed.");
				}
			}
		}
		final boolean isNestedWordAutomaton = !complementState.getOperand().getVpAlphabet().getCallAlphabet().isEmpty();
		final StringBuilder builder = new StringBuilder(listN.size() + listC.size() + listS.size() + listB.size());
		builder.append(OPEN_PARENTHESIS);
		prettyprintCollectionOfStates(builder, listN, isNestedWordAutomaton);
		builder.append(COMMA);
		prettyprintCollectionOfStates(builder, listC, isNestedWordAutomaton);
		builder.append(COMMA);
		prettyprintCollectionOfStates(builder, listS, isNestedWordAutomaton);
		builder.append(COMMA);
		prettyprintCollectionOfStates(builder, listB, isNestedWordAutomaton);
		builder.append(CLOSE_PARENTHESIS);
		return builder.toString();
	}

	private static void prettyprintCollectionOfStates(final StringBuilder builder,
			final List<Pair<StateWithRankInfo<String>, String>> collection, final boolean isNestedWordAutomaton) {
		if (collection.isEmpty()) {
			builder.append(EMPTY_SET);
			return;
		}

		builder.append(OPEN_BRACE);
		boolean isFirst = true;
		for (final Pair<StateWithRankInfo<String>, String> pair : collection) {
			if (isFirst) {
				isFirst = false;
			} else {
				builder.append(COMMA);
			}
			if (isNestedWordAutomaton) {
				// @formatter:off
				builder.append(OPEN_PARENTHESIS)
						.append(pair.getFirst())
						.append(COMMA)
						.append(pair.getSecond())
						.append(CLOSE_PARENTHESIS);
				// @formatter:on
			} else {
				builder.append(pair.getSecond());
			}
		}
		builder.append(CLOSE_BRACE);
	}

	@Override
	public String buchiComplementDeterministicNonFinal(final String state) {
		return "NonFinal:" + state;
	}

	@Override
	public String buchiComplementDeterministicFinal(final String state) {
		return "Final:" + state;
	}

	@Override
	public String merge(final Collection<String> states) {
		if (states == null) {
			return EMPTY_SET;
		}
		final StringBuilder builder = new StringBuilder(states.size() * MINIMUM_LIST_SIZE);
		builder.append(OPEN_BRACE);
		String separator = EMPTY_STRING;
		for (final String state : states) {
			// @formatter:off
			builder.append(separator)
					.append(state);
			// @formatter:on
			separator = COMMA_SPACE;
		}
		return builder.append(CLOSE_BRACE).toString();
	}

	/**
	 * @param downState
	 *            Down state.
	 * @param upState
	 *            up state
	 * @return double decker content
	 */
	public static String createDoubleDeckerContent(final String downState, final String upState) {
		return '<' + downState + COMMA + upState + '>';
	}

	@Override
	public String buchiComplementSvw(final Integer stateNb, final Integer tmaNb) {
		final StringBuilder builder = new StringBuilder();
		// @formatter:off
		builder.append(OPEN_PARENTHESIS)
				.append(stateNb)
				.append(COMMA)
				.append(tmaNb)
				.append(CLOSE_PARENTHESIS);
		// @formatter:on
		return builder.toString();
	}

	@Override
	public String finitePrefix2net(final Condition<?, String> condition) {
		return condition.toString();
	}

	@Override
	public String senwa(final String entry, final String state) {
		return state + " (entry " + entry + CLOSE_PARENTHESIS;
	}

	private static void buchiComplementFkvHelper(final StringBuilder builder,
			final StateWithRankInfo<String> stateWithInfo) {
		// @formatter:off
		builder.append(stateWithInfo.getState())
				.append(COMMA);
		// @formatter:on
		if (stateWithInfo.hasRank()) {
			builder.append(stateWithInfo.getRank());
			if (stateWithInfo.isInO()) {
				builder.append(X_STRING);
			}
		} else {
			builder.append(INFINITY);
		}
	}

	private static void buchiComplementNcsbHelperRankTwo(final List<Pair<StateWithRankInfo<String>, String>> listC,
			final List<Pair<StateWithRankInfo<String>, String>> listB, final StateWithRankInfo<String> downState,
			final StateWithRankInfo<String> upState) {
		listC.add(new Pair<>(downState, upState.getState()));
		if (upState.isInO()) {
			listB.add(new Pair<>(downState, upState.getState()));
		}
	}

	/**
	 * @author Yong Li (liyong@ios.ac.cn)
	 * */
	@Override
	public String buchiComplementNcsbSimple(final int id) {
		return "s" + id;
	}

	@Override
	public String relabel(final String state, final int i) {
		return "q" + i;
	}

}
