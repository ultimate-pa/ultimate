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
	private final FunctionSymbol mIntand;
	// private final LinkedHashMap<Term, Integer> mWidthMap; // maps integer term to der corresponding Bv width
	// TODO flag for optimizations / delta

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
			// mGetWidth.put(mVariableMap.get(term), Integer.valueOf(mVariableMap.get(term).getSort().getIndices()[0]));
			setResult(mVariableMap.get(term));
			return;
		} else if (term instanceof ConstantTerm) {
			// TODO 2^k and other special cases
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

	private boolean uts(final Term term, final int width) {
		if (!SmtSortUtils.isIntSort(term.getSort())) {
			return false;
		}
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("-")) {
				if (appTerm.getParameters()[0] instanceof ApplicationTerm) {
					final ApplicationTerm twoTimesMod = (ApplicationTerm) appTerm.getParameters()[0];
					if (twoTimesMod.getFunction().getName().equals("*")) {
						if (twoTimesMod.getParameters()[0] instanceof ConstantTerm) { // LHS is 2
							final ConstantTerm two = (ConstantTerm) twoTimesMod.getParameters()[0];
							if (two.getValue().equals(Rational.TWO)) {
								if (twoTimesMod.getParameters()[1] instanceof ApplicationTerm) { // RHS is mod t 2^k-1
									final ApplicationTerm mod = (ApplicationTerm) twoTimesMod.getParameters()[1];
									if (mod.getParameters()[0] instanceof ApplicationTerm) {

										if (mod.getParameters()[0].equals(appTerm.getParameters()[1])) {

											if (mod.getParameters()[1] instanceof ConstantTerm) {
												final ConstantTerm halfwidth = (ConstantTerm) mod.getParameters()[1];
												if (halfwidth.getValue().equals(Rational.valueOf(
														BigInteger.valueOf(2).pow(width - 1), BigInteger.ONE))) {
													return true;
												}
											}
										}
									}
								}

							}
						}

					}
				}
			}

		}
		return false;
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
		// TODO sign and zerofill
		if (!SmtSortUtils.isBitvecSort(term.getSort())) {
			return term;
		}
		final int oldwidth = Integer.valueOf(term.getSort().getIndices()[0]);

		if (oldwidth == targetwidth) {
			return term;
		}
		if (oldwidth > targetwidth) {

			System.out.println(term + "  " + oldwidth + " " + targetwidth);

			throw new UnsupportedOperationException("TODO MOd optimization");
			// throw new UnsupportedOperationException("target width needs to be greater or equal to old width");
		} else {
			final int extendby = targetwidth - oldwidth;
			final BigInteger[] indices = new BigInteger[1];
			indices[0] = BigInteger.valueOf(extendby);
			if (!argsigned) {
				// TODO
				return BitvectorUtils.termWithLocalSimplification(mScript, "zero_extend", indices, term);
			} else {
				return BitvectorUtils.termWithLocalSimplification(mScript, "sign_extend", indices, term);
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

	// private boolean isPowerOfTwo(final Rational r) {
	// final BigInteger i = r.numerator();
	// if (i != BigInteger.ZERO) {
	// return ((i.and((i.subtract(BigInteger.ONE)))) == BigInteger.ZERO);
	// } else {
	// return false;
	// }
	// }

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
			throw new UnsupportedOperationException("TODO Sign");
		}
		throw new UnsupportedOperationException("Unknown Sign");

	}

	/*
	 * TODO non-recursive
	 * TODO optimize, sollte aber korrekt sein geht nur kleinere width
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
					throw new UnsupportedOperationException("TODO handle here");
				}
				// return here
			} else if (appTerm.getParameters().length == 1) {
				if (appTerm.getFunction().getName().equals("-")) {
					width = getWidth(appTerm.getParameters()[0]);
				} else {
					throw new UnsupportedOperationException("TODO handle here");
				}
				// return here
			}
			if (appTerm.getFunction().getName().equals("select")) {
				final Term array;
				{
					final MultiDimensionalSelect mds = MultiDimensionalSelect.convert(appTerm);
					if (mds != null) {
						array = mds.getArray();
					} else {
						final MultiDimensionalSelectOverNestedStore mdsons = MultiDimensionalSelectOverNestedStore
								.convert(mScript, appTerm);
						if (mdsons != null) {
							array = mdsons.getNestedStore().getArray();
						} else {
							throw new UnsupportedOperationException("unable to compute width: " + appTerm);
						}
					}
				}
				final Term bvArray = mVariableMap.get(array);
				final MultiDimensionalSort mdSort = new MultiDimensionalSort(bvArray.getSort());
				final Sort valueSort = mdSort.getArrayValueSort();
				width = Integer.valueOf(valueSort.getIndices()[0]);
			} else {

				int maxWidth = getWidth(appTerm.getParameters()[0]);
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
						// TODO case t1 * 2^k + t2
						// TODO nested +
						width = maxWidth + 1;
						break;
					}
					case "-": {
						if (appTerm.getParameters()[0] instanceof ConstantTerm) {
							// 2^k-t //TODO k = getwidth(t), was aber wenn k anderervalue?
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
						width = maxWidth; // TODO next 2er potenz von RHS

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
			if (isSigned(term)) {
				for (final Term argument : appTerm.getParameters()) {
					if (!isSigned(argument)) {
						// nur wenn auch width argument = width term??
						return width + 1;
					}
				}
			}
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
		if (fsym.equals(mIntand)) {
			for (int i = 0; i < args.length; i++) {
				newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
			}
			setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvand", null, newargs));
			return;
		}
		if (fsym.isIntern()) {
			switch (fsym.getName()) {
			case "=": {
				for (int i = 0; i < args.length; i++) {
					newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
				}
				setResult(SmtUtils.equality(mScript, newargs));
				return;
			}
			case "<": {
				// if (uts(appTerm.getParameters()[0], width) && uts(appTerm.getParameters()[1], width)) {
				// if (newargs[0] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[0];
				// newargs[0] = appArg.getParameters()[1];
				// }
				// if (newargs[1] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[1];
				// newargs[1] = appArg.getParameters()[1];
				// }
				// setResult(
				// BitvectorUtils.termWithLocalSimplification(mScript, "bvslt", null, newargs[0], newargs[1]));
				// return;
				// }
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvslt", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvult", null, newargs));
					return;
				}
			}
			case "<=": {
				// if (uts(appTerm.getParameters()[0], width) && uts(appTerm.getParameters()[1], width)) {
				// if (newargs[0] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[0];
				// newargs[0] = appArg.getParameters()[1];
				// }
				// if (newargs[1] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[1];
				// newargs[1] = appArg.getParameters()[1];
				// }
				// setResult(
				// BitvectorUtils.termWithLocalSimplification(mScript, "bvsle", null, newargs[0], newargs[1]));
				// return;
				// }
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvsle", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvule", null, newargs));
					return;
				}
			}
			case ">=": {
				// if (uts(appTerm.getParameters()[0], width) && uts(appTerm.getParameters()[1], width)) {
				// if (newargs[0] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[0];
				// newargs[0] = appArg.getParameters()[1];
				// }
				// if (newargs[1] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[1];
				// newargs[1] = appArg.getParameters()[1];
				// }
				// setResult(
				// BitvectorUtils.termWithLocalSimplification(mScript, "bvsge", null, newargs[0], newargs[1]));
				// return;
				// }
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvsge", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvuge", null, newargs));
					return;
				}
			}
			case ">": {
				// if (uts(appTerm.getParameters()[0], width) && uts(appTerm.getParameters()[1], width)) {
				// if (newargs[0] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[0];
				// newargs[0] = appArg.getParameters()[1];
				// }
				// if (newargs[1] instanceof ApplicationTerm) {
				// final ApplicationTerm appArg = (ApplicationTerm) newargs[1];
				// newargs[1] = appArg.getParameters()[1];
				// }
				// setResult(
				// BitvectorUtils.termWithLocalSimplification(mScript, "bvsgt", null, newargs[0], newargs[1]));
				// return;
				// }
				if (isSigned(appTerm)) {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvsgt", null, newargs));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvugt", null, newargs));
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
					// TODO what if first arguent is signed?

					if (isPowerOfTwo(value)) {

						final Term extendby = BitvectorUtils.constructTerm(mScript,
								new BitvectorConstant(BigInteger.ZERO, BigInteger.valueOf(getTwoExponent(value))));

						setResult(
								BitvectorUtils.termWithLocalSimplification(mScript, "concat", null, args[0],
								extendby));
						return;
					}
				}

				for (int i = 0; i < args.length; i++) {
					newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
				}
				setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvmul", null, newargs));
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
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvsub", null, newargs));
					return;
				}

			}
			case "mod": {
				if (appTerm.getParameters()[1] instanceof ConstantTerm) {
					// case t mod 2^i
					final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
					final Rational value = (Rational) constTerm.getValue();
					// TODO what if first arguent is signed?

					if (isPowerOfTwo(value)) {
						final BigInteger[] indices = new BigInteger[2];
						indices[0] = BigInteger.valueOf(getTwoExponent(value) - 1);
						indices[1] = BigInteger.valueOf(0);
						// übersetzen zu (mod s t)-> (extract s)
						// TODO argument smaller than expoenent
						setResult(BitvectorUtils.termWithLocalSimplification(mScript, "extract", indices, args[0]));
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
					final Term bvsmod = BitvectorUtils.termWithLocalSimplification(mScript, "bvsmod", null, newargs);
					final Term ifTerm = SmtUtils.binaryEquality(mScript,
							BitvectorUtils.termWithLocalSimplification(mScript, "extract", indices, newargs[1]), one);
					final Term thenTerm = BitvectorUtils.termWithLocalSimplification(mScript, "bvneg", null,
							BitvectorUtils.termWithLocalSimplification(mScript, "bvsub", null, newargs[1], bvsmod));
					setResult(Util.ite(mScript, ifTerm, thenTerm, bvsmod));
					return;
				} else {
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], getWidth(appTerm), isSigned(oldargs[i]));
					}
					setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvurem", null, newargs));
					return;
				}
			}
			case "div": {
				if (appTerm.getParameters()[1] instanceof ConstantTerm) {
					// case t mod 2^i
					final ConstantTerm constTerm = (ConstantTerm) appTerm.getParameters()[1];
					final Rational value = (Rational) constTerm.getValue();
					// TODO what if first arguent is signed?

					if (isPowerOfTwo(value)) {
						final BigInteger[] indices = new BigInteger[2];
						final int oldwidth = Integer.valueOf(args[0].getSort().getIndices()[0]);
						indices[0] = BigInteger.valueOf(oldwidth - 1);
						indices[1] = BigInteger.valueOf(getTwoExponent(value));
						// übersetzen zu (mod s t)-> (extract s)
						// TODO argument smaller than expoenent
						setResult(BitvectorUtils.termWithLocalSimplification(mScript, "extract", indices, args[0]));
						return;
					}
				}
				if (isSigned(appTerm)) {
					final int width = getWidth(appTerm);
					for (int i = 0; i < args.length; i++) {
						newargs[i] = bringTermToWidth(args[i], width, isSigned(oldargs[i]));
					}
					final Term bvsdiv = BitvectorUtils.termWithLocalSimplification(mScript, "bvsdiv", null, newargs);
					final Term bvurem = BitvectorUtils.termWithLocalSimplification(mScript, "bvurem", null, newargs);
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
							BitvectorUtils.termWithLocalSimplification(mScript, "extract", indices, newargs[0]);
					final Term extractRHS =
							BitvectorUtils.termWithLocalSimplification(mScript, "extract", indices, newargs[1]);

					final Term bvsub = BitvectorUtils.termWithLocalSimplification(mScript, "bvsub", null, bvsdiv, oneK);
					final Term bvadd = BitvectorUtils.termWithLocalSimplification(mScript, "bvadd", null, bvsdiv, oneK);

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
						setResult(BitvectorUtils.termWithLocalSimplification(mScript, "bvudiv", null, newargs));
						return;



				}
			}
			case "ite": {
				setResult(mScript.term("ite", args[0], args[1], args[2]));
				return;
			}
			case "abs": {
				throw new UnsupportedOperationException("Unexpected function in back-translation " + fsym.getName());
			}

			default:
				setResult(SmtUtils.termWithLocalSimplification(mScript, fsym, args));
				return;

			}
		}

		super.convertApplicationTerm(appTerm, newargs);
	}

	private boolean isZero(final Term term) {
		if (term instanceof ConstantTerm) {
			final ConstantTerm cnst = (ConstantTerm) term;
			if (cnst.getValue().equals(Rational.ZERO)) {
				return true;
			}
		}
		return false;
	}

	private boolean isMaxNumberPlusOne(final Term term, final int width) {
		assert SmtSortUtils.isIntSort(term.getSort());
		if (term instanceof ConstantTerm) {
			final ConstantTerm ct = (ConstantTerm) term;
			final Rational rational = (Rational) ct.getValue();
			if (rational.equals(Rational.valueOf(BigInteger.TWO.pow(width), BigInteger.ONE))) {
				return true;
			}
			// negated maxnumber
			if (rational.isNegative()) {
				if (rational.negate().equals(Rational.valueOf(BigInteger.TWO.pow(width), BigInteger.ONE))) {
					return true;
				}
			}

		}
		return false;
	}

	private boolean isMaxNumberPlusOneHalf(final Term term, final int width) {
		assert SmtSortUtils.isIntSort(term.getSort());
		if (term instanceof ConstantTerm) {
			final ConstantTerm ct = (ConstantTerm) term;
			final Rational rational = (Rational) ct.getValue();
			if (rational.equals(Rational.valueOf(BigInteger.TWO.pow(width).divide(BigInteger.TWO), BigInteger.ONE))) {
				return true;
			}
			// negated maxnumber
			if (rational.isNegative()) {
				if (rational.negate()
						.equals(Rational.valueOf(BigInteger.TWO.pow(width).divide(BigInteger.TWO), BigInteger.ONE))) {
					return true;
				}
			}

		}
		return false;
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
