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

/**
 * Thrown when the value analysis cannot compute a concrete value, e.g. for an uninterpreted function, a quantifier, a
 * floating-point operation or a division by zero, whose result SMT-LIB leaves open. The caller drops the step, which
 * keeps the analysis an under-approximation.
 * <p>
 * It is thrown on the hot path of the search for every unsupported step, so it records no stack trace.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class UnsupportedTermException extends RuntimeException {
	private static final long serialVersionUID = 1L;

	public UnsupportedTermException(final String message) {
		super(message, null, false, false);
	}
}
