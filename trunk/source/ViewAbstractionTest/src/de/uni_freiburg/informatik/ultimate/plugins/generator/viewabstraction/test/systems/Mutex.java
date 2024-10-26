/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ViewAbstractionTest Library.
 *
 * The ULTIMATE ViewAbstractionTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ViewAbstractionTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ViewAbstractionTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ViewAbstractionTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ViewAbstractionTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.systems;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Configuration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.GlobalVarUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.IRule;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.Program;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.programs.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ListIndependence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.viewabstraction.test.ViewTest.ITestProgram;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Mutex implements ITestProgram<ProgramState<Integer, Mutex.IncDecLocation>> {
	enum IncDecLocation {
		MINUS("⊖"), PLUS("⨁");

		private final String mStr;

		private IncDecLocation(final String str) {
			mStr = str;
		}

		@Override
		public String toString() {
			return mStr;
		}
	}

	private final int mBound;
	private final IRule<ProgramState<Integer, IncDecLocation>> increment;
	private final IRule<ProgramState<Integer, IncDecLocation>> decrement;

	public Mutex(final int bound) {
		mBound = bound;
		increment = new GlobalVarUpdate<>(IncDecLocation.MINUS, IncDecLocation.PLUS,
				i -> (mBound == -1 || i < mBound) ? i + 1 : null);
		decrement = new GlobalVarUpdate<>(IncDecLocation.PLUS, IncDecLocation.MINUS, i -> i - 1);
	}

	@Override
	public Program<ProgramState<Integer, Mutex.IncDecLocation>> getTransitions() {
		return new Program<>(null, List.of(increment, decrement));
	}

	@Override
	public Configuration<ProgramState<Integer, Mutex.IncDecLocation>> init(final int parameter) {
		final ProgramState<Integer, Mutex.IncDecLocation> controller = new ProgramState.ControllerState<>(0);
		final ProgramState<Integer, Mutex.IncDecLocation> thread = new ProgramState.ThreadState<>(IncDecLocation.MINUS);
		final var threads =
				new ImmutableList<>(IntStream.range(0, parameter).mapToObj(i -> thread).collect(Collectors.toList()));
		return new Configuration<>(new ImmutableList<>(controller, threads));
	}

	@Override
	public boolean isBad(final Configuration<ProgramState<Integer, Mutex.IncDecLocation>> config) {
		return config.stream().anyMatch(s -> s.isThreadState() && s.getThreadState() == IncDecLocation.PLUS)
				&& config.stream().filter(s -> s.isControllerState()).findAny().get().getControllerState() == 0;
	}

	public <S> IIndependenceRelation<S, IRule<ProgramState<Integer, IncDecLocation>>> getIndependence() {
		if (mBound == -1) {
			return new ListIndependence<>(List.of(new Pair<>(increment, decrement), new Pair<>(decrement, increment)));
		}
		return null;
	}
}