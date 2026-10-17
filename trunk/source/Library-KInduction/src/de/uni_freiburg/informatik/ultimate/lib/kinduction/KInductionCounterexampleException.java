/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction;

/**
 * Thrown when k-induction proved the program unsafe but no concrete run over the abstraction could be produced for
 * it. The verdict itself is not in doubt when this is thrown - only our ability to express it as a counterexample.
 * <p>
 * Kept apart from {@link AssertionError}, which {@link KInductionCounterexampleBuilder} and its caller use for the
 * genuinely impossible: a model that does not fit the encoding, or a trace check that contradicts k-induction.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class KInductionCounterexampleException extends RuntimeException {

	private static final long serialVersionUID = 1L;

	public KInductionCounterexampleException(final String message) {
		super(message);
	}
}
