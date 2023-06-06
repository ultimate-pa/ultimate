/*
 * Copyright (C) 2021-2022 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

public class IntToBvBackTranslation extends TermTransformer {
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private final LinkedHashMap<Term, Term> mVariableMap; // Maps Int Var to Bv Var
	private final Set<Term> mConstraintSet; // Set of all constraints
	private final FunctionSymbol mIntand; // uninterpreted function symbol, maps two integer to an integer, represents
											// bit-wise and

	/*
	 * Extension to the TermTransformer. Transforms an formula over integers to a formula over bit-vectors.
	 * Can transform formulas with arrays and quantifers. Every variable in the integer formula has to be in the
	 * variableMap.
	 */
	public IntToBvBackTranslation(final ManagedScript mgdscript, final LinkedHashMap<Term, Term> variableMap,
			final Set<Term> constraintSet, final FunctionSymbol intand) {
		mMgdScript = mgdscript;
		mScript = mgdscript.getScript();
		mVariableMap = variableMap;
		mConstraintSet = constraintSet;
		mIntand = intand;
	}

	@Override
	public void convert(final Term term) {
		if (mConstraintSet.contains(term)) {
			setResult(mScript.term("true"));
			return;
		}
		if (mVariableMap.containsKey(term)) {
			setResult(mVariableMap.get(term));
			return;
		} else

			if (term instanceof ConstantTerm) {
			setResult(translateConst((ConstantTerm) term));
			return;
		} else if (term instanceof TermVariable) {
			throw new UnsupportedOperationException("Cannot translate AuxVars back to Bitvector Sort " + term);
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getParameters().length == 0) {
				if (SmtUtils.isConstant(appTerm)) {
					throw new UnsupportedOperationException("Cannot translate AuxVars back to Bitvector Sort " + term);
				}
			}
		}
		super.convert(term);

	}


	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final HashSet<TermVariable> newTermVars = new HashSet();
		if (newBody != old.getSubformula()) {
			for (int i = 0; i < old.getVariables().length; i++) {
				if (mVariableMap.containsKey(old.getVariables()[i])) {
					newTermVars.add((TermVariable) mVariableMap.get(old.getVariables()[i]));

				} else {
					newTermVars.add(old.getVariables()[i]);
				}
			}
			setResult(SmtUtils.quantifier(mScript, old.getQuantifier(), newTermVars, newBody));
			return;
		} else {
			super.postConvertQuantifier(old, newBody);
		}

	}

	private Term bringTermToWidth(final Term term, final int targetwidth, final boolean argsigned) {
		if (!SmtSortUtils.isBitvecSort(term.getSort())) {
			return term;
		}
		final int oldwidth = Integer.valueOf(term.getSort().getIndices()[0]);

		if (oldwidth == targetwidth) {
			return term;
		}
		if (oldwidth > targetwidth) {
			// TODO sometimes necessary if targetwidth is given by select term
			final BigInteger[] indices = new BigInteger[2];
				indices[0] = BigInteger.valueOf(targetwidth - 1);
				indices[1] = BigInteger.valueOf(0);

				return BitvectorUtils.unfTerm(mScript, "extract", indices, term);


		} else {
			final int extendby = targetwidth - oldwidth;
			final BigInteger[] indices = new BigInteger[1];
			indices[0] = BigInteger.valueOf(extendby);
			if (!argsigned) {
				return BitvectorUtils.unfTerm(mScript, "zero_extend", indices, term);
			} else {
				return BitvectorUtils.unfTerm(mScript, "sign_extend", indices, term);
			}
		}

	}

	private int getTwoExponent(final Rational r) {
		final BigInteger i = r.numerator();
		final int value = Integer.lowestOneBit(i.intValue());
		if (Integer.highestOneBit(i.intValue()) == value) {
			return i.bitLength() - 1;
		}
		throw new UnsupportedOperationException("Not a power of two");
	}

	private boolean isPowerOfTwo(final Rational r) {

		BigInteger i = r.numerator();
		if (BigInteger.ZERO.compareTo(i) == 0)
			return false;

		while (BigInteger.ONE.compareTo(i) != 0) {
			if (i.mod(BigInteger.TWO) != BigInteger.ZERO) {
				return false;
			}
			i = i.divide(BigInteger.TWO);
		}
		return true;
	}

	private boolean isSigned(final Term term) {
		// assert SmtSortUtils.isBitvecSort(term.getSort());
		if (mVariableMap.containsKey(term)) {
			return false;
		} else if (term instanceof ConstantTerm) {
			return ((Rational) ((ConstantTerm) term).getValue()).isNegative(); // translated to bvneg(-)
		} else if (term instanceof TermVariable) {
			// returns length of the bitvector of the absolute value
			return false;
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getParameters().length == 0) {
				if (SmtUtils.isConstant(appTerm)) {
					return false;
				}
				throw new UnsupportedOperationException("Cannot translate AuxVars back to Bitvector Sort " + term);
			}
			if (appTerm.getFunction().getName().equals("-")) {
				return true;
			}
			if (appTerm.getFunction().getName().equals("mod")) { // euclidean remainder always positive
				return false;
			}
			boolean sign = false;
			for (int i = 0; i < appTerm.getParameters().length; i++) {
				final Term argument = appTerm.getParameters()[i];
				sign = sign || isSigned(argument);
			}

			return sign;
		} else if (term instanceof QuantifiedFormula) {
			throw new UnsupportedOperationException("Unsupported sign of quantified formula");
		}
		throw new UnsupportedOperationException("Unknown Sign");

	}

	private Term getInnerMostArray(final Term appTerm) {
		Term array;
		if (appTerm instanceof TermVariable) {
			return appTerm;
		}
		final MultiDimensionalSelect mds = MultiDimensionalSelect.of(appTerm);
		if (mds.getIndex().size() > 0) {
			array = mds.getArray();
		} else {
			final MultiDimensionalSelectOverNestedStore mdsons =
					MultiDimensionalSelectOverNestedStore.convert(mScript, appTerm);
			if (mdsons != null) {
				// array = mdsons.getNestedStore().getArray();
				array = mdsons.getSelect().getArray();
			} else {
				throw new UnsupportedOperationException("unable to compute width: " + appTerm);
			}
		}
		if (array instanceof ApplicationTerm) {
			final ApplicationTerm appArray = (ApplicationTerm) array;
			if (appArray.getFunction().getName().equals("select")) {
				array = getInnerMostArray(appArray.getParameters()[0]);
			}
			else if (appArray.getFunction().getName().equals("store")) {
				array = getInnerMostArray(appArray.getParameters()[0]);
			}
		}
		return array;
	}

	/*
	 * TODO non-recursive
	 * TODO optimize, smaller widths
	 */
	private Integer getWidth(final Term term) {
		int width = 0;

		if (mVariableMap.containsKey(term)) {
			return Integer.valueOf(mVariableMap.get(term).getSort().getIndices()[0]);
		} else if (term instanceof ConstantTerm) {
			// returns length of the bitvector of the absolute value
			final Rational value = ((Rational) ((ConstantTerm) term).getValue());
			final int minWidth = value.abs().numerator().bitLength();
			if (minWidth == 0) {
				width = 1;
			} else {
				width = minWidth;
			}
			// if (value.isNegative()) {
			// return width + 1;
			// } else {
			return width;
			// }
		} else if (term instanceof TermVariable) {
			throw new UnsupportedOperationException("Unknown width of AuxVar");
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getParameters().length == 0) {
				if (SmtUtils.isConstant(appTerm)) {
					throw new UnsupportedOperationException("Unknown width of AuxVar");
				} else {
					throw new UnsupportedOperationException("Unkexpected term: " + appTerm);
				}
				// return here
			} else if (appTerm.getParameters().length == 1) {
				if (appTerm.getFunction().getName().equals("-")) {
					width = getWidth(appTerm.getParameters()[0]);
				} else {
					throw new UnsupportedOperationException("Unkexpected term: " + appTerm);
				}
				// return here
			}

			if (appTerm.getFunction().getName().equals("select")) {
				final Term array = getInnerMostArray(appTerm);
				final Term bvArray = mVariableMap.get(array);

				if (bvArray == null) {
					throw new UnsupportedOperationException("Unknown Array: " + array);
				}
				final MultiDimensionalSort mdSort = new MultiDimensionalSort(bvArray.getSort());
				final Sort valueSort = mdSort.getArrayValueSort();
				width = Integer.valueOf(valueSort.getIndices()[0]);
			} else {
				int maxWidth;
				if (!SmtSortUtils.isIntSort(appTerm.getParameters()[0].getSort())) {
					// TODO ite terms
					// throw new UnsupportedOperationException("Cannot calculate width " + term);#
					maxWidth = 1;
				} else {
					maxWidth = getWidth(appTerm.getParameters()[0]);
				}

				for (int i = 1; i < appTerm.getParameters().length; i++) {
					final Term argument = appTerm.getParameters()[i];
					final int argWidth = getWidth(argument);
					if (argWidth > maxWidth) {
						maxWidth = argWidth;
					}
				}
				width = maxWidth;
				final FunctionSymbol fsym = appTerm.getFunction();

				if (fsym.isIntern()) {
					switch (fsym.getName()) {
					case "*": {
						if (appTerm.getParameters().length == 2) {
							if (appTerm.getParameters()[0] instanceof ConstantTerm) {
								// case t * 2^i
								final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[0];
								final Rational value = (Rational) constTerm.getValue();
								if (isPowerOfTwo(value)) {
									width = getWidth(appTerm.getParameters()[1]) + getTwoExponent(value);
									break;
								}
							} else if (appTerm.getParameters()[1] instanceof ConstantTerm) {
								// case t * 2^i
								final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
								final Rational value = (Rational) constTerm.getValue();
								if (isPowerOfTwo(value)) {
									width = getWidth(appTerm.getParameters()[0]) + getTwoExponent(value);
									break;
								}
							}
						}
						width = maxWidth * 2;
						break;

					}
					case "+": {
						width = maxWidth + 1;
						break;
					}
					case "-": {
						if (appTerm.getParameters()[0] instanceof ConstantTerm) {
							// 2^k-t //TODO k = getwidth(t), but k has a different value?
							if (isPowerOfTwo((Rational) ((ConstantTerm) appTerm.getParameters()[0]).getValue())) {
								width = getWidth(appTerm.getParameters()[1]);
								break;
							}
						}
						width = maxWidth + 1;

						break;
					}
					case "mod": {
						if (appTerm.getParameters()[1] instanceof ConstantTerm) {
							// case t mod 2^i
							final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
							final Rational value = (Rational) constTerm.getValue();
							if (isPowerOfTwo(value)) {
								width = getTwoExponent(value);
								break;
							}
						}
						width = maxWidth;

						break;
					}
					case "div": {
						if (appTerm.getParameters()[1] instanceof ConstantTerm) {
							// case t mod 2^i
							final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
							final Rational value = (Rational) constTerm.getValue();
							if (isPowerOfTwo(value)) {
								width = getWidth(appTerm.getParameters()[0]) - getTwoExponent(value);
								break;
							}
						}
						width = maxWidth;
						break;
					}
					default: {
						width = maxWidth;
						break;
					}
					}
				}
			}
			// if (isSigned(term)) { // TODO necessary?
			// for (final Term argument : appTerm.getParameters()) {
			// if (!isSigned(argument)) {
			// // in crease witdth by one for a sign bit
			// return width + 1;
			// }
			// }
			// }
			return width;
		}
		throw new UnsupportedOperationException("Unexpected Term " + term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] args) {
		final Term[] newargs = new Term[args.length];
		final Term[] oldargs = appTerm.getParameters();
		// Constraints are always true in BV Theory
		if (mConstraintSet.contains(appTerm)) {
			setResult(mScript.term("true"));
			return;
		}

		final FunctionSymbol fsym = appTerm.getFunction();
		if (fsym.equals(mIntand) || fsym.getName().equals("intand")) {
			for (int i = 0; i < args.length; i++) {
				newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
			}
			setResult(BitvectorUtils.unfTerm(mScript, "bvand", null, newargs));
			return;
		}
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "=": {
				for (int i = 0; i < args.length; i++) {
					if (SmtSortUtils.isIntSort(appTerm.getParameters()[0].getSort())) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					} else {
						newargs[i] = args[i];
					}

				}
				setResult(SmtUtils.equality(mScript, newargs));
				return;
			}
			case "<": {
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvslt", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvult", null, newargs));
					return;
				}
			}
			case "<=": {
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvsle", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvule", null, newargs));
					return;
				}
			}
			case ">=": {
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvsge", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvuge", null, newargs));
					return;
				}
			}
			case ">": {
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvsgt", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvugt", null, newargs));
					return;
				}
			}
			case "+": {
				for (int i = 0; i < args.length; i++) {
					newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
				}

				setResult(SmtUtils.binaryBitvectorSum(mScript, null, newargs));

				return;
			}
			case "*": {
				if (appTerm.getParameters()[1] instanceof ConstantTerm) {
					// case t * 2^i
					final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
					final Rational value = (Rational) constTerm.getValue();
					if (isPowerOfTwo(value)) {

						final Term extendby = BitvectorUtils.constructTerm(mScript,
								new BitvectorConstant(BigInteger.ZERO, BigInteger.valueOf(getTwoExponent(value))));

						setResult(
								BitvectorUtils.unfTerm(mScript, "concat", null, args[0],
								extendby));
						return;
					}
				}

				for (int i = 0; i < args.length; i++) {
					newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
				}
				setResult(BitvectorUtils.unfTerm(mScript, "bvmul", null, newargs));
				return;
			}
			case "-": {
				if (appTerm.getParameters().length == 1) {
					assert !(args[0] instanceof ConstantTerm);
					setResult(
							mScript.term("bvneg", bringTermToWidth(args[0], getWidth(appTerm), isSigned(oldargs[0]))));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvsub", null, newargs));
					return;
				}

			}
			case "mod": {
				if (appTerm.getParameters()[1] instanceof ConstantTerm) {
					// case t mod 2^i
					final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
					final Rational value = (Rational) constTerm.getValue();
					if (isPowerOfTwo(value)) {
						final BigInteger[] indices = new BigInteger[2];
						indices[0] = BigInteger.valueOf(getTwoExponent(value) - 1);
						indices[1] = BigInteger.valueOf(0);
						// translate: (mod s t)-> (extract s)
						// TODO argument smaller than expoenent
						setResult(BitvectorUtils.unfTerm(mScript, "extract", indices, args[0]));
						return;
					}
				}
				if (isSigned(appTerm)) {
					final int width = getWidth(appTerm);
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], width, isSigned(oldargs[i]));
					}
					final Term one = BitvectorUtils.constructTerm(mScript,
							new BitvectorConstant(BigInteger.ONE, BigInteger.valueOf(1)));

					final BigInteger[] indices = new BigInteger[2];
					indices[0] = BigInteger.valueOf(width - 1);
					indices[1] = BigInteger.valueOf(width - 1);
					final Term bvsmod = BitvectorUtils.unfTerm(mScript, "bvsmod", null, newargs);
					final Term ifTerm = SmtUtils.binaryEquality(mScript,
							BitvectorUtils.unfTerm(mScript, "extract", indices, newargs[1]), one);
					final Term thenTerm = BitvectorUtils.unfTerm(mScript, "bvneg", null,
							BitvectorUtils.unfTerm(mScript, "bvsub", null, newargs[1], bvsmod));
					setResult(Util.ite(mScript, ifTerm, thenTerm, bvsmod));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.unfTerm(mScript, "bvurem", null, newargs));
					return;
				}
			}
			case "div": {
				if (appTerm.getParameters()[1] instanceof ConstantTerm) {
					// case t mod 2^i
					final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
					final Rational value = (Rational) constTerm.getValue();
					if (isPowerOfTwo(value)) {
						final BigInteger[] indices = new BigInteger[2];
						final int oldwidth = Integer.valueOf(args[0].getSort().getIndices()[0]);
						final int twoExpo = getTwoExponent(value);

						if(twoExpo > oldwidth - 1) {
							final Term zero = BitvectorUtils.constructTerm(mScript,
									new BitvectorConstant(BigInteger.ZERO, BigInteger.valueOf(1)));
							setResult(zero);
							return;
						} else {

						indices[0] = BigInteger.valueOf(oldwidth - 1);
						indices[1] = BigInteger.valueOf(twoExpo);


						setResult(BitvectorUtils.unfTerm(mScript, "extract", indices, args[0]));
						return;
					}
					}
				}
				if (isSigned(appTerm)) {
					// bit-vector term that represent euclidean division with signed arguments
					final int width = getWidth(appTerm);
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], width, isSigned(oldargs[i]));
					}
					final Term bvsdiv = BitvectorUtils.unfTerm(mScript, "bvsdiv", null, newargs);
					final Term bvurem = BitvectorUtils.unfTerm(mScript, "bvurem", null, newargs);
					final Term zeroK = BitvectorUtils.constructTerm(mScript,
							new BitvectorConstant(BigInteger.ZERO, BigInteger.valueOf(width)));
					final Term oneK = BitvectorUtils.constructTerm(mScript,
							new BitvectorConstant(BigInteger.ONE, BigInteger.valueOf(width)));
					final Term zero = BitvectorUtils.constructTerm(mScript,
							new BitvectorConstant(BigInteger.ZERO, BigInteger.valueOf(1)));
					final Term one = BitvectorUtils.constructTerm(mScript,
							new BitvectorConstant(BigInteger.ONE, BigInteger.valueOf(1)));
					final BigInteger[] indices = new BigInteger[2];
					indices[0] = BigInteger.valueOf(width - 1);
					indices[1] = BigInteger.valueOf(width - 1);
					final Term extractLHS =
							BitvectorUtils.unfTerm(mScript, "extract", indices, newargs[0]);
					final Term extractRHS =
							BitvectorUtils.unfTerm(mScript, "extract", indices, newargs[1]);

					final Term bvsub = BitvectorUtils.unfTerm(mScript, "bvsub", null, bvsdiv, oneK);
					final Term bvadd = BitvectorUtils.unfTerm(mScript, "bvadd", null, bvsdiv, oneK);

					final Term ifTerm3 = SmtUtils.and(mScript, SmtUtils.binaryEquality(mScript, extractLHS, one),
							SmtUtils.binaryEquality(mScript, extractRHS, one));
					final Term ite3 = Util.ite(mScript, ifTerm3, bvadd, bvsdiv);

					final Term ifTerm2 = SmtUtils.and(mScript, SmtUtils.binaryEquality(mScript, extractLHS, one),
							SmtUtils.binaryEquality(mScript, extractRHS, zero));
					final Term ite2 = Util.ite(mScript, ifTerm2, bvsub, ite3);

					final Term ifTerm = SmtUtils.not(mScript, SmtUtils.binaryEquality(mScript, bvurem, zeroK));
					final Term thenTerm = ite2;
					final Term ite1 = Util.ite(mScript, ifTerm, thenTerm, bvsdiv);

					setResult(ite1);
					return;
				} else {
						for (int i = 0; i < args.length; i++) {
							newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
						}
						setResult(BitvectorUtils.unfTerm(mScript, "bvudiv", null, newargs));
						return;



				}
			}
			case "ite": {
				setResult(mScript.term("ite", args[0], args[1], args[2]));
				return;
			}
			case "select": {
				final var index = bringTermToWidth(args[1],
						Integer.parseInt(args[0].getSort().getArguments()[0].getIndices()[0]), false);
				if (Integer.parseInt(args[0].getSort().getArguments()[0].getIndices()[0]) != Integer
						.parseInt(index.getSort().getIndices()[0])) {
					// TODO why does bringTermToWidth not work?
					throw new AssertionError(String.format("Cannot access array with %sbit indices via %sbit term.",
							Integer.parseInt(args[0].getSort().getArguments()[0].getIndices()[0]),
							Integer.parseInt(index.getSort().getIndices()[0])));
				}
				setResult(mScript.term("select", args[0], index));
				return;
			}
			case "store": {

				final Sort bitVecArraySort = getArrayValueSort(args[0].getSort());

				setResult(mScript.term("store", args[0], bringTermToWidth(args[1],
						Integer.parseInt(args[0].getSort().getArguments()[0].getIndices()[0]), false),
						bringTermToWidth(args[2], Integer.parseInt(bitVecArraySort.getIndices()[0]),
								false)));
				return;
			}
			case "abs": {
				throw new UnsupportedOperationException("Unexpected function in back-translation " + fsym.getName());
			}
			case "const": {
				throw new UnsupportedOperationException("Unable to translate const array back. Don't know width of index. Look-ahead needed.");
			}

			default:
				setResult(SmtUtils.unfTerm(mScript, fsym, args));
				return;

			}
		}

		super.convertApplicationTerm(appTerm, newargs);
	}

	private Sort getArrayValueSort(final Sort array) {
		assert SmtSortUtils.isArraySort(array);
		final Sort argSort = array.getArguments()[1];
		if (SmtSortUtils.isBitvecSort(argSort)) {
			return argSort;
		} else if (SmtSortUtils.isArraySort(argSort)) {
			return getArrayValueSort(argSort);
		}else {
			throw new UnsupportedOperationException("Unexpected Array Value Sort");
		}
	}

	private Term translateConst(final ConstantTerm value) {
		assert value.getValue() instanceof Rational;

		if (((Rational) value.getValue()).isNegative()) {
			// .bitLength() returns 2's complement representation but we want binary and negate afterwards
			final int width = getWidth(value);
			return SmtUtils.rational2Term(mScript, (Rational) value.getValue(),
					SmtSortUtils.getBitvectorSort(mScript, width + 1));
		} else {

			final int width = getWidth(value);
			return SmtUtils.rational2Term(mScript, (Rational) value.getValue(),
					SmtSortUtils.getBitvectorSort(mScript, width));
		}
	}
}
