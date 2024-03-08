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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.views;

import java.util.ArrayList;
import java.util.List;

public class LocalRule<S> implements IRule<S> {
	private final S mSource;
	private final S mTarget;

	public LocalRule(final S source, final S target) {
		mSource = source;
		mTarget = target;
	}

	@Override
	public boolean isApplicable(final Configuration<S> config) {
		return config.contains(mSource);
	}

	@Override
	public List<Configuration<S>> successors(final Configuration<S> config) {
		final var result = new ArrayList<Configuration<S>>();

		for (int i = 0; i < config.size(); ++i) {
			final S state = config.get(i);
			if (state.equals(mSource)) {
				result.add(config.replace(i, mTarget));
			}
		}
		return result;
	}

	@Override
	public int extensionSize() {
		return 0;
	}
}
