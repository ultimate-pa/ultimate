/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.Optional;
import java.util.function.BooleanSupplier;

/**
 * Represents a test function that can optionally support to be canceled.
 */
@FunctionalInterface
public interface IVariantTestFunction {
	/**
	 * Cancelable test function. The return value is only optional if the test is actually canceled, i.e. the isCanceled
	 * predicate returns true. Otherwise a result has to be supplied.
	 *
	 * @param variant
	 *            reduced source code variant to test
	 * @param isCanceled
	 *            function that can be polled to see if no result is required
	 * @return valid test result indicating if the variant should be kept or not if not canceled, optional result
	 *         otherwise
	 */
	default Optional<Boolean> cancelableTest(final String variant, final BooleanSupplier isCanceled) {
		return Optional.of(test(variant));
	}
	
	/**
	 * Non cancelable test function.
	 *
	 * @param variant
	 *            reduced source code to test
	 * @return test result indicating if the variant should be kept or not
	 */
	boolean test(String variant);
}
