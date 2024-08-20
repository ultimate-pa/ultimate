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

import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Configuration;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Quantifier;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.GlobalRule.Range;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.LocalRule;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.Program;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views.ViewTest.ITestProgram;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

public class BurnsSimple implements ITestProgram<BurnsSimple.B> {
	public enum B {
		green, white, black, yellow, blue, red
	}

	@Override
	public Program<B> getTransitions() {
		final Predicate<B> ybr = Set.of(B.yellow, B.blue, B.red)::contains;
		final Predicate<B> gwb = Set.of(B.green, B.white, B.black)::contains;
		return new Program<>(null,
				List.of(new LocalRule<>(B.green, B.white),
						new GlobalRule<>(B.white, B.green, Range.LESS, Quantifier.EXISTS, ybr),
						new GlobalRule<>(B.white, B.black, Range.LESS, Quantifier.FORALL, gwb),
						new LocalRule<>(B.black, B.yellow),
						new GlobalRule<>(B.yellow, B.green, Range.LESS, Quantifier.EXISTS, ybr),
						new GlobalRule<>(B.yellow, B.blue, Range.LESS, Quantifier.FORALL, gwb),
						new GlobalRule<>(B.blue, B.red, Range.GREATER, Quantifier.FORALL, gwb),
						new LocalRule<>(B.red, B.green)));
	}

	@Override
	public Configuration<B> init(final int parameter) {
		return new Configuration<>(
				new ImmutableList<>(IntStream.range(0, parameter).mapToObj(i -> B.green).collect(Collectors.toList())));
	}

	@Override
	public boolean isBad(final Configuration<B> config) {
		return config.stream().filter(s -> s == B.red).limit(2).count() > 1;
	}

}