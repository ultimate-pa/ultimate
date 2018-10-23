package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigInteger;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

/**
 * Factory for creating wrapper functions that handle the IRA syntactic sugar rules. The SMTLIB standard permits to call
 * a function with two Real arguments with a mixture of Int and Real. This is syntactic sugar for casting the Int
 * parameters to Real using the to_real function. This factory creates wrapper function symbols with the correct mixture
 * of Int and Real arguments. These are defined functions and their function definition calls the original function
 * symbol with the correct to_real casts.
 *
 * @author Jochen Hoenicke
 */
public class IRAWrapperFactory {
	final UnifyHash<FunctionSymbol> mInstances = new UnifyHash<>();

	/**
	 * Create an IRA wrapper function for name for the given parameter sorts. This is a new function symbol whose
	 * definition casts all integer parameters to real parameters using the {@code to_real} function. If the parameter
	 * count does not match, or if not all parameters are real or integer this returns null.
	 *
	 * For associative functions this creates a wrapper for every used sequence of sorts. E.g., it may create the
	 * function {@code (define-fun + ((Real a) (Int b) (Real c)) (+ a (to_real b) c))}.
	 *
	 * @param theory
	 *            the underlying theory.
	 * @param name
	 *            the unwrapped function symbol. It is assumed that it takes two real parameters except for "ite".
	 * @param indices
	 *            optional indices, null for no indices.
	 * @param paramSorts
	 *            the parameter sorts for the wrapper function.
	 * @param resultType
	 *            the result type specified by SMTLIB {@code (as ..)}; null if no result type specified.
	 * @return null if an error occured, otherwise the wrapping function symbol.
	 */
	public FunctionSymbol createWrapper(Theory theory, String name, final BigInteger[] indices, Sort[] paramSorts,
			final Sort resultType) {
		final Sort realSort = theory.getRealSort();
		final Sort intSort = theory.getNumericSort();
		final FunctionSymbol fsym;
		/*
		 * First check that paramSorts is correct.
		 */
		if (name.equals("ite") && indices == null) {
			/* ite expects a bool and two int/real mixed arguments. */
			if (paramSorts[0] != theory.getBooleanSort()) {
				return null;
			}
			if ((paramSorts[1] != intSort || paramSorts[2] != realSort)
					&& (paramSorts[1] != realSort || paramSorts[2] != intSort)) {
				return null;
			}
			/* Create the base function symbol. */
			fsym = theory.getFunctionWithResult(name, indices, resultType,
					new Sort[] { theory.getBooleanSort(), realSort, realSort });
			if (fsym == null) {
				return null;
			}
		} else {
			/* Else all arguments must be Int or Real. At least one must be Int. */
			boolean hasInt = false;
			for (int i = 0; i < paramSorts.length; i++) {
				if (paramSorts[i] == intSort) {
					hasInt = true;
				} else if (paramSorts[i] != realSort) {
					return null;
				}
			}
			if (!hasInt) {
				return null;
			}
			/* Create the base function symbol. */
			fsym = theory.getFunctionWithResult(name, indices, resultType, realSort, realSort);
			if (fsym == null) {
				return null;
			}
			/* Check if the number of parameters is two or the symbol is associative. */
			if (paramSorts.length != 2 && (paramSorts.length < 2 || (fsym.mFlags & FunctionSymbol.ASSOCMASK) == 0)) {
				return null;
			}
		}

		/* Check if we already created a wrapper and return it. */
		final int hash = fsym.hashCode() ^ Arrays.hashCode(paramSorts);
		for (final FunctionSymbol func : mInstances.iterateHashCode(hash)) {
			if (((ApplicationTerm) func.getDefinition()).getFunction() == fsym
					&& Arrays.equals(func.mParamSort, paramSorts)) {
				return func;
			}
		}

		/* Create the wrapping definition */
		TermVariable[] defVars = new TermVariable[paramSorts.length];
		Term[] wrappedArgs = new Term[paramSorts.length];
		for (int i = 0; i < paramSorts.length; i++) {
			defVars[i] = theory.createTermVariable("x" + i, paramSorts[i]);
			wrappedArgs[i] = paramSorts[i] == intSort ? theory.term("to_real", defVars[i]) : defVars[i];
		}
		Term definition = theory.term(fsym, wrappedArgs);
		assert definition != null;

		/* Create the function symbol */
		FunctionSymbol wrapper = new FunctionSymbol(fsym.getName(), fsym.getIndices(), paramSorts, fsym.getReturnSort(),
				defVars, definition, (fsym.mFlags & ~FunctionSymbol.ASSOCMASK));
		mInstances.put(hash, wrapper);
		return wrapper;
	}
}
