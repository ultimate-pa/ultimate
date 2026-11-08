/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE ValueAnalysis Library.
 *
 * The ULTIMATE ValueAnalysis Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ValueAnalysis Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ValueAnalysis Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ValueAnalysis Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ValueAnalysis Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.valueanalysis;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.ArrayValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.BitvectorValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.BoolValue;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.IConcreteValue.NumberValue;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * The values the value analysis tries for a variable whose value a step leaves open: a havoc, an auxiliary variable,
 * or a read of a variable that was never assigned. The values are fixed and few, the ones that most often reach a
 * violation in C programs: zero, one, minus one and the boundaries of the machine integers. Since every choice is
 * checked against the step's formula, any choice keeps the analysis sound; the pool only decides which executions it
 * finds.
 * <p>
 * The candidates come in a fixed order, so the search is deterministic. A strategy that wants other values, e.g.
 * random ones, can subclass this and override {@link #computeCandidates(Sort)}.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class NondeterminismPool {
	private static final BigInteger INT_MAX = BigInteger.valueOf(Integer.MAX_VALUE);
	private static final BigInteger INT_MIN = BigInteger.valueOf(Integer.MIN_VALUE);
	private static final BigInteger UINT_MAX = BigInteger.ONE.shiftLeft(32).subtract(BigInteger.ONE);

	private final Map<Sort, List<IConcreteValue>> mCache = new HashMap<>();

	/**
	 * @return the values to try for a variable of {@code sort}, never empty
	 * @throws UnsupportedTermException
	 *             if the analysis has no values of this sort, e.g. floating point or an uninterpreted sort
	 */
	public List<IConcreteValue> candidates(final Sort sort) {
		final List<IConcreteValue> cached = mCache.get(sort);
		if (cached != null) {
			return cached;
		}
		final List<IConcreteValue> result = List.copyOf(computeCandidates(sort));
		mCache.put(sort, result);
		return result;
	}

	/**
	 * The values to try first for {@code var}, before the literals of the step's formula and before
	 * {@link #candidates(Sort)}: what a subclass knows about this very variable, e.g. the values a solver's model gave
	 * it. None by default.
	 *
	 * @param var
	 *            the program variable behind the open variable of the step, {@code null} for an auxiliary variable
	 * @param sort
	 *            the sort of the open variable
	 */
	public List<IConcreteValue> preferred(final IProgramVar var, final Sort sort) {
		return List.of();
	}

	protected List<IConcreteValue> computeCandidates(final Sort sort) {
		if (SmtSortUtils.isBoolSort(sort)) {
			return List.of(BoolValue.FALSE, BoolValue.TRUE);
		}
		if (SmtSortUtils.isIntSort(sort)) {
			return integers(BigInteger.ZERO, BigInteger.ONE, BigInteger.ONE.negate(), INT_MAX, INT_MIN, UINT_MAX);
		}
		if (SmtSortUtils.isRealSort(sort)) {
			final List<IConcreteValue> result = new ArrayList<>(integers(BigInteger.ZERO, BigInteger.ONE,
					BigInteger.ONE.negate()));
			result.add(new NumberValue(Rational.valueOf(1, 2)));
			return result;
		}
		if (SmtSortUtils.isBitvecSort(sort)) {
			final BigInteger width = new BigInteger(sort.getRealSort().getIndices()[0]);
			final BigInteger signBit = BigInteger.ONE.shiftLeft(width.intValueExact() - 1);
			final List<IConcreteValue> result = new ArrayList<>();
			for (final BigInteger value : List.of(BigInteger.ZERO, BigInteger.ONE, BigInteger.ONE.negate(),
					signBit.subtract(BigInteger.ONE), signBit)) {
				final IConcreteValue candidate = new BitvectorValue(new BitvectorConstant(value, width));
				// For narrow widths some of these coincide.
				if (!result.contains(candidate)) {
					result.add(candidate);
				}
			}
			return result;
		}
		if (SmtSortUtils.isArraySort(sort)) {
			// One array only: trying several would multiply the choices by the size of a whole memory.
			final Sort valueSort = sort.getRealSort().getArguments()[1];
			return List.of(ArrayValue.constant(candidates(valueSort).get(0)));
		}
		throw new UnsupportedTermException("no values of sort " + sort);
	}

	private static List<IConcreteValue> integers(final BigInteger... values) {
		final List<IConcreteValue> result = new ArrayList<>(values.length);
		for (final BigInteger value : values) {
			result.add(new NumberValue(Rational.valueOf(value, BigInteger.ONE)));
		}
		return result;
	}
}
