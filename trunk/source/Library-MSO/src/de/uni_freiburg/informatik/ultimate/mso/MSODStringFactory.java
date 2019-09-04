/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE MSO Library package.
 *
 * The ULTIMATE MSO Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSO Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSO Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSO Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSO Library package library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigInteger;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementFkvStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;

/**
 * A {@link IStateFactory} for {@link String}s.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODStringFactory implements IIntersectionStateFactory<String>, IUnionStateFactory<String>,
		ISinkStateFactory<String>, IDeterminizeStateFactory<String>, IMinimizationStateFactory<String>,
		IBuchiIntersectStateFactory<String>, IBuchiComplementFkvStateFactory<String> {

	static final String EMPTY = "€";
	static final String STATE = "q";
	static final String SINK = "∅SinkState";
	BigInteger mCounter;

	public MSODStringFactory() {
		mCounter = BigInteger.ZERO;
	}

	@Override
	public String createEmptyStackState() {
		return EMPTY;
	}

	@Override
	public String intersection(final String state1, final String state2) {
		return newString();
	}

	@Override
	public String union(final String state1, final String state2) {
		return newString();
	}

	@Override
	public String createSinkStateContent() {
		return SINK;
	}

	@Override
	public String determinize(final Map<String, Set<String>> down2up) {
		return newString();
	}

	@Override
	public String merge(final Collection<String> states) {
		return newString();
	}

	@Override
	public String intersectBuchi(final String state1, final String state2, final int track) {
		return newString();
	}

	@Override
	public String buchiComplementFkv(final LevelRankingState<?, String> complementState) {
		return newString();
	}

	/**
	 * Returns an unique string.
	 */
	private String newString() {
		final StringBuilder builder = new StringBuilder();
		builder.append(STATE).append(mCounter.toString());
		mCounter = mCounter.add(BigInteger.ONE);

		return builder.toString();
	}
}