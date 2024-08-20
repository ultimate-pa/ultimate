/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtilsTest Library.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.systems;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Configuration;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Range;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.IRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.LocalRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Program;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.ITestProgram;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

// version of Burns protocol as in Ahmed Rezine's PhD thesis
public class BurnsRezine implements ITestProgram<Pair<BurnsRezine.Burns, Boolean>> {
	public enum Burns {
		q1, q2, q3, q4, q5, q6, q7;
	}

	@Override
	public Program<Pair<BurnsRezine.Burns, Boolean>> getTransitions() {
		final List<IRule<Pair<BurnsRezine.Burns, Boolean>>> rules = Arrays.asList(
				// first rule
				new LocalRule<>(new Pair<>(Burns.q1, true), new Pair<>(Burns.q2, false)),
				new LocalRule<>(new Pair<>(Burns.q1, false), new Pair<>(Burns.q2, false)),

				// second rule
				new GlobalRule<>(new Pair<>(Burns.q2, true), new Pair<>(Burns.q2, true), Range.LESS, Quantifier.EXISTS,
						Pair::getSecond),
				new GlobalRule<>(new Pair<>(Burns.q2, false), new Pair<>(Burns.q2, false), Range.LESS,
						Quantifier.EXISTS, Pair::getSecond),

				// third rule
				new GlobalRule<>(new Pair<>(Burns.q2, true), new Pair<>(Burns.q3, true), Range.LESS, Quantifier.FORALL,
						s -> !s.getSecond()),
				new GlobalRule<>(new Pair<>(Burns.q2, false), new Pair<>(Burns.q3, false), Range.LESS,
						Quantifier.FORALL, s -> !s.getSecond()),

				// fourth rule
				new LocalRule<>(new Pair<>(Burns.q3, true), new Pair<>(Burns.q4, true)),
				new LocalRule<>(new Pair<>(Burns.q3, false), new Pair<>(Burns.q4, true)),

				// fifth rule
				new GlobalRule<>(new Pair<>(Burns.q4, true), new Pair<>(Burns.q1, true), Range.LESS, Quantifier.EXISTS,
						Pair::getSecond),
				new GlobalRule<>(new Pair<>(Burns.q4, false), new Pair<>(Burns.q1, false), Range.LESS,
						Quantifier.EXISTS, Pair::getSecond),

				// sixth rule
				new GlobalRule<>(new Pair<>(Burns.q4, true), new Pair<>(Burns.q5, true), Range.LESS, Quantifier.FORALL,
						s -> !s.getSecond()),
				new GlobalRule<>(new Pair<>(Burns.q4, false), new Pair<>(Burns.q5, false), Range.LESS,
						Quantifier.FORALL, s -> !s.getSecond()),

				// seventh rule
				new GlobalRule<>(new Pair<>(Burns.q5, true), new Pair<>(Burns.q6, true), Range.GREATER,
						Quantifier.FORALL, s -> !s.getSecond()),
				new GlobalRule<>(new Pair<>(Burns.q5, false), new Pair<>(Burns.q6, false), Range.GREATER,
						Quantifier.FORALL, s -> !s.getSecond()),

				// eigth rule
				new LocalRule<>(new Pair<>(Burns.q6, true), new Pair<>(Burns.q7, false)),
				new LocalRule<>(new Pair<>(Burns.q6, false), new Pair<>(Burns.q7, false)),

				// ninth rule
				new LocalRule<>(new Pair<>(Burns.q7, true), new Pair<>(Burns.q1, true)),
				new LocalRule<>(new Pair<>(Burns.q7, false), new Pair<>(Burns.q1, false))

		);

		return new Program<>(null, rules);
	}

	@Override
	public Configuration<Pair<BurnsRezine.Burns, Boolean>> init(final int parameter) {
		final var state = new Pair<>(Burns.q1, false);
		return new Configuration<>(ViewTest.repeat(parameter, state));
	}

	@Override
	public boolean isBad(final Configuration<Pair<BurnsRezine.Burns, Boolean>> config) {
		return config.stream().filter(s -> s.getFirst() == Burns.q6).limit(2).count() > 1;
	}
}