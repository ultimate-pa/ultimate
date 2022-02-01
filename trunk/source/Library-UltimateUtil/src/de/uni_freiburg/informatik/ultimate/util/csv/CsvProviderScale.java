/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.csv;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Scales data of an {@link ICsvProvider}.
 * <p>
 * NOTE: Data contains shallow copies, i.e., modifications affect both the original data and this wrapper. Copy the
 * original to avoid such problems.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderScale implements ICsvProviderTransformer<String> {
	/**
	 * Modes for scaling.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum ScaleMode {
		/**
		 * Integer division with rounding to the nearest integer.
		 */
		DIV_INT
	}
	
	private final Map<String, Pair<Double, ScaleMode>> mColumn2Scale;
	
	/**
	 * @param column2Scale
	 *            Map from column title to scale mode (unchanged columns should just be omitted).
	 */
	public CsvProviderScale(final Map<String, Pair<Double, ScaleMode>> column2Scale) {
		mColumn2Scale = column2Scale;
	}
	
	@Override
	public ICsvProvider<String> transform(final ICsvProvider<String> csv) {
		int col = -1;
		final int rows = csv.getRowHeaders().size();
		for (final String columnTitle : csv.getColumnTitles()) {
			++col;
			final Pair<Double, ScaleMode> scale = mColumn2Scale.get(columnTitle);
			if (scale == null) {
				continue;
			}
			
			for (int i = 0; i < rows; ++i) {
				final BigDecimal oldVal = new BigDecimal(csv.getRow(i).get(col));
				final double newVal = computeScale(oldVal, scale);
				csv.getRow(i).set(col, Double.toString(newVal));
			}
		}
		return csv;
	}
	
	@SuppressWarnings("squid:S1698")
	private static double computeScale(final BigDecimal oldVal, final Pair<Double, ScaleMode> scale) {
		final double result;
		switch (scale.getSecond()) {
			case DIV_INT:
				final BigDecimal divisor = BigDecimal.valueOf(scale.getFirst());
				if (divisor == BigDecimal.ZERO) {
					result = Double.NaN;
					break;
				}
				final BigDecimal divRes = oldVal.divide(divisor, RoundingMode.HALF_UP);
				final BigDecimal asInt = divRes.setScale(0, RoundingMode.HALF_UP);
				result = asInt.doubleValue();
				break;
			default:
				throw new IllegalArgumentException("Unknown scale mode: " + scale.getSecond());
		}
		return result;
	}
}
