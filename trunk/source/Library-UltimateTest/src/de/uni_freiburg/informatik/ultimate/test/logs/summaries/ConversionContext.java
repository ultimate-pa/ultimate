/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.logs.summaries;

import java.math.BigDecimal;
import java.math.RoundingMode;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public final class ConversionContext {
	private enum ConversionType {
		KEEP, DIVIDE, PERCENT, BESTFITNUMBER
	}

	private ConversionType mType;
	private String mUnit;
	private String mFactor;
	private int mPrecision;

	private ConversionContext() {

	}

	public static ConversionContext Keep() {
		final ConversionContext c = new ConversionContext();
		c.mType = ConversionType.KEEP;
		c.mUnit = "";
		return c;
	}

	public static ConversionContext Keep(String unit) {
		final ConversionContext c = new ConversionContext();
		c.mType = ConversionType.KEEP;
		c.mUnit = unit;
		return c;
	}

	public static ConversionContext Percent(boolean escape, int precision) {
		if (precision < 0) {
			throw new IllegalArgumentException("precision has to be positive");
		}

		final ConversionContext c = new ConversionContext();
		c.mType = ConversionType.PERCENT;
		if (escape) {
			c.mUnit = "\\%";
		} else {
			c.mUnit = "%";
		}
		c.mFactor = "100";
		c.mPrecision = precision;

		return c;
	}

	public static ConversionContext BestFitNumber() {
		final ConversionContext c = new ConversionContext();
		c.mType = ConversionType.BESTFITNUMBER;
		return c;
	}

	public static ConversionContext Divide(int divisor, int precision, String unit) {
		if (precision < 0) {
			throw new IllegalArgumentException("precision has to be positive");
		}
		if (divisor == 0) {
			throw new IllegalArgumentException("divisor may not be 0");
		}
		final ConversionContext c = new ConversionContext();
		c.mType = ConversionType.DIVIDE;
		c.mFactor = Integer.toString(divisor);
		c.mUnit = unit;
		c.mPrecision = precision;
		return c;
	}

	public String makeHumanReadable(String input) {
		switch (mType) {
		case PERCENT:
			return makeHumanReadablePercent(input, mUnit, mPrecision);
		case BESTFITNUMBER:
			return makeHumanReadableNumber(input);
		case KEEP:
			return input + mUnit;
		case DIVIDE:
			return makeHumanReadableDivide(input, mFactor, mPrecision, mUnit);
		default:
			return "-";
		}
	}

	private String makeHumanReadableDivide(String input, String divisor, int precision, String unit) {
		final BigDecimal current = convert(input);
		if (current == null) {
			return "-";
		}

		try {
			return current.divide(new BigDecimal(divisor)).setScale(precision, RoundingMode.HALF_UP).toString() + unit;
		} catch (final Exception ex) {
			return "NaN";
		}
	}

	private String makeHumanReadablePercent(String input, String unit, int precision) {
		final BigDecimal current = convert(input);
		if (current == null) {
			return "-";
		}

		try {
			return current.multiply(new BigDecimal("100")).setScale(precision, RoundingMode.HALF_UP).toString() + unit;
		} catch (final Exception ex) {
			return "NaN";
		}
	}

	private String makeHumanReadableNumber(String input) {
		final BigDecimal current = convert(input);
		if (current == null) {
			return "-";
		}

		try {
			return CoreUtil.humanReadableNumber(current.longValue());
		} catch (final Exception ex) {
			return "NaN";
		}
	}

	private BigDecimal convert(String input) {
		try {
			return new BigDecimal(input);
		} catch (final Exception ex) {
			return null;
		}
	}
}
