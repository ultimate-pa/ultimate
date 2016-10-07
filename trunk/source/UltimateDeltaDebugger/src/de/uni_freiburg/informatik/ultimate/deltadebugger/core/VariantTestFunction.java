package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import java.util.Optional;
import java.util.function.BooleanSupplier;

/**
 * Represents a test function that can optionally support to be canceled.
 */
@FunctionalInterface
public interface VariantTestFunction {

	/**
	 * Non cancelable test function.
	 * 
	 * @param variant
	 *            reduced source code to test
	 * @return test result indicating if the variant should be kept or not
	 */
	boolean test(String variant);

	/**
	 * Cancelable test function. The return value is only optional if the test
	 * is actually canceled, i.e. the isCanceled predicate returns true.
	 * Otherwise a result has to be supplied.
	 * 
	 * @param variant
	 * @param variant
	 *            reduced source code variant to test
	 * @param isCanceled
	 *            function that can be polled to see if no result is required
	 * @return valid test result indicating if the variant should be kept or not
	 *         if not canceled, optional result otherwise
	 */
	default Optional<Boolean> cancelableTest(String variant, BooleanSupplier isCanceled) {
		return Optional.of(test(variant));
	}
}
