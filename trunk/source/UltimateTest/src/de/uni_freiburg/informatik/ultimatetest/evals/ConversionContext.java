package de.uni_freiburg.informatik.ultimatetest.evals;

import java.math.BigDecimal;
import java.math.RoundingMode;
import de.uni_freiburg.informatik.ultimate.util.Utils;

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
		ConversionContext c = new ConversionContext();
		c.mType = ConversionType.KEEP;
		c.mUnit = "";
		return c;
	}

	public static ConversionContext Keep(String unit) {
		ConversionContext c = new ConversionContext();
		c.mType = ConversionType.KEEP;
		c.mUnit = unit;
		return c;
	}

	public static ConversionContext Percent(boolean escape, int precision) {
		if (precision < 0) {
			throw new IllegalArgumentException("precision has to be positive");
		}

		ConversionContext c = new ConversionContext();
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
		ConversionContext c = new ConversionContext();
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
		ConversionContext c = new ConversionContext();
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
		BigDecimal current = convert(input);
		if (current == null) {
			return "-";
		}

		try {
			return current.divide(new BigDecimal(divisor)).setScale(precision, RoundingMode.HALF_UP).toString() + unit;
		} catch (Exception ex) {
			return "NaN";
		}
	}

	private String makeHumanReadablePercent(String input, String unit, int precision) {
		BigDecimal current = convert(input);
		if (current == null) {
			return "-";
		}

		try {
			return current.multiply(new BigDecimal("100")).setScale(precision, RoundingMode.HALF_UP).toString() + unit;
		} catch (Exception ex) {
			return "NaN";
		}
	}

	private String makeHumanReadableNumber(String input) {
		BigDecimal current = convert(input);
		if (current == null) {
			return "-";
		}

		try {
			return Utils.humanReadableNumber(current.longValue());
		} catch (Exception ex) {
			return "NaN";
		}
	}

	private BigDecimal convert(String input) {
		try {
			return new BigDecimal(input);
		} catch (Exception ex) {
			return null;
		}
	}
}