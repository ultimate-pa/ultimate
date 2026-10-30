/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * The sort of the integers the encoding adds itself: the pc, the transition selector and the index of the
 * {@link CallStack}. It is {@code Int} unless the program is bit-precise, i.e. none of its variables involves
 * {@code Int} or {@code Real}. Then it is a bitvector, because the solver of a bit-precise analysis (e.g. bitwuzla)
 * need not support {@code Int} at all.
 * <p>
 * Bitvector values are read as two's complement: a stack pointer may start anywhere, and only the differences of
 * stack pointers matter, which Java's {@code int} arithmetic wraps exactly like {@code bvadd} at this width.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class CounterSort {
	/**
	 * Covers the pc values and transitions of any program we can build, and the stack pointer up to far more
	 * activations than k-induction unrolls steps.
	 */
	private static final int BITVECTOR_WIDTH = 32;

	private final Sort mSort;

	private CounterSort(final Sort sort) {
		mSort = sort;
	}

	/**
	 * @return {@code Int}, unless no program variable of {@code csToolkit} involves {@code Int} or {@code Real}
	 */
	public static CounterSort forProgram(final Script script, final CfgSmtToolkit csToolkit) {
		final List<IProgramVar> vars = new ArrayList<>(csToolkit.getSymbolTable().getGlobals());
		for (final String procedure : csToolkit.getProcedures()) {
			vars.addAll(csToolkit.getSymbolTable().getLocals(procedure));
		}
		if (involvesNumbers(vars)) {
			return new CounterSort(SmtSortUtils.getIntSort(script));
		}
		return new CounterSort(SmtSortUtils.getBitvectorSort(script, BITVECTOR_WIDTH));
	}

	private static boolean involvesNumbers(final Collection<? extends IProgramVar> vars) {
		for (final IProgramVar pv : vars) {
			if (involvesNumbers(pv.getTermVariable().getSort())) {
				return true;
			}
		}
		return false;
	}

	/** Also looks into the index and value sorts of an array. */
	private static boolean involvesNumbers(final Sort sort) {
		if (SmtSortUtils.isNumericSort(sort)) {
			return true;
		}
		for (final Sort argument : sort.getArguments()) {
			if (involvesNumbers(argument)) {
				return true;
			}
		}
		return false;
	}

	public Sort getSort() {
		return mSort;
	}

	public boolean isBitvector() {
		return SmtSortUtils.isBitvecSort(mSort);
	}

	/** The literal for {@code value}. */
	public Term value(final Script script, final int value) {
		if (isBitvector()) {
			// Two's complement, the inverse of toInt
			final BigInteger unsigned = BigInteger.valueOf(value).mod(BigInteger.ONE.shiftLeft(BITVECTOR_WIDTH));
			return BitvectorUtils.constructTerm(script, unsigned, mSort);
		}
		return SmtUtils.constructIntValue(script, BigInteger.valueOf(value));
	}

	/**
	 * The value of a literal of this sort, e.g. from a model.
	 *
	 * @param description
	 *            what the literal is the value of, for the error message
	 */
	public int toInt(final Term literal, final String description) {
		if (isBitvector()) {
			final BitvectorConstant constant =
					literal == null ? null : BitvectorUtils.constructBitvectorConstant(literal);
			if (constant == null) {
				throw notALiteral(literal, description);
			}
			BigInteger value = constant.getValue();
			if (value.testBit(BITVECTOR_WIDTH - 1)) {
				value = value.subtract(BigInteger.ONE.shiftLeft(BITVECTOR_WIDTH));
			}
			return value.intValueExact();
		}
		final Rational rational = literal == null ? null : SmtUtils.tryToConvertToLiteral(literal);
		if (rational == null || !rational.isIntegral()) {
			throw notALiteral(literal, description);
		}
		return rational.numerator().intValueExact();
	}

	/**
	 * The pc, the transition selector and the stack pointer are literals of this sort by construction, so anything
	 * else means the model does not fit the encoding, which is a bug rather than an unsupported case.
	 */
	private AssertionError notALiteral(final Term literal, final String description) {
		return new AssertionError("the k-induction model gives " + literal + " for " + description
				+ ", which is not a literal of sort " + mSort);
	}

	@Override
	public String toString() {
		return mSort.toString();
	}
}
