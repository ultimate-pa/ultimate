package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.FastUPRUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class OctagonTransformer extends NonRecursive {

	private enum InequalitySide {
		NONE, LEFT, RIGHT
	}

	private enum InequalityType {
		NONE, LESSER, LESSER_EQUAL,
	}

	private final HashSet<Term> mCheckedTerms;
	private TermVariable mFirstVar;
	private TermVariable mSecondVar;
	private boolean mFirstNegative;
	private boolean mSecondNegative;
	private BigDecimal mFirstCoefficient;
	private BigDecimal mSecondCoefficient;
	private final OctagonDetector mOctagonDetector;

	private BigDecimal mValue;

	private InequalityType mType;

	private final ManagedScript mManagedScript;
	private final HashSet<Term> mAdditionalTerms;
	private final FastUPRUtils mUtils;

	public OctagonTransformer(FastUPRUtils utils, ManagedScript managedScript, OctagonDetector detector) {
		mOctagonDetector = detector;
		mUtils = utils;
		mCheckedTerms = new HashSet<>();
		mValue = new BigDecimal(0);
		mManagedScript = managedScript;
		mAdditionalTerms = new HashSet<>();
	}

	private static class OctagonTermWalker implements NonRecursive.Walker {

		private final Term mTerm;
		private final InequalitySide mSide;
		private final boolean mNegate;

		OctagonTermWalker(Term t, InequalitySide side) {
			this(t, side, false);
		}

		OctagonTermWalker(Term t, InequalitySide side, boolean negate) {
			mTerm = t;
			mSide = side;
			mNegate = negate;
		}

		OctagonTermWalker(Term t, boolean b) {
			this(t, InequalitySide.NONE, b);
		}

		@Override
		public void walk(NonRecursive engine) {
			// TODO Auto-generated method stub
			if (mSide == InequalitySide.NONE) {
				((OctagonTransformer) engine).transformTerm(mTerm, mNegate);
			} else {
				((OctagonTransformer) engine).transformTermSide(mTerm, mSide, mNegate);
			}
		}

	}

	public OctagonConjunction transform(Term term) {
		return transform(mOctagonDetector.getConjunctSubTerms(term));
	}

	public OctagonConjunction transform(HashSet<Term> terms) {
		mCheckedTerms.clear();
		mAdditionalTerms.clear();
		mUtils.debug("Starting Term to OctagonTransformation");

		final OctagonConjunction octagon = new OctagonConjunction();

		for (final Term t : terms) {
			mUtils.debug("Getting Value from:" + t.toString());
			resetTerm();
			run(new OctagonTermWalker(t, InequalitySide.NONE));

			if (mType == InequalityType.LESSER)
				mValue = mValue.subtract(new BigDecimal(1));
			mUtils.debug("Value is:" + mValue.toString());

			if (mFirstVar == null) {
				mUtils.debug("ERROR");
			} else if (mSecondVar == null) {
				mValue = mValue.multiply(new BigDecimal(2));
				octagon.addTerm(new OneVarOctTerm(mValue, mFirstVar, mFirstNegative));
			} else {
				octagon.addTerm(new TwoVarOctTerm(mValue, mFirstVar, mFirstNegative, mSecondVar, mSecondNegative));
			}
		}

		for (final Term t : mAdditionalTerms) {
			mUtils.debug("Getting Value from:" + t.toString());
			resetTerm();
			run(new OctagonTermWalker(t, InequalitySide.NONE));

			if (mType == InequalityType.LESSER)
				mValue = mValue.subtract(new BigDecimal(1));
			mUtils.debug("Value is:" + mValue.toString());

			if (mFirstVar == null) {
				mUtils.debug("ERROR");
			} else if (mSecondVar == null) {
				mValue = mValue.multiply(new BigDecimal(2));
				octagon.addTerm(new OneVarOctTerm(mValue, mFirstVar, mFirstNegative));
			} else {
				octagon.addTerm(new TwoVarOctTerm(mValue, mFirstVar, mFirstNegative, mSecondVar, mSecondNegative));
			}
		}

		mUtils.debug("Octagon:");
		mUtils.debug(octagon.toString());

		return octagon;
	}

	public ParametricOctMatrix getMatrix(OctagonConjunction conjunc, ArrayList<TermVariable> variables) {
		mUtils.debug(">> Converting OctagonConjunction to Matrix");
		mUtils.debug("> Conjunction: " + conjunc.toString());
		final ArrayList<OctagonTerm> terms = conjunc.getTerms();
		final ParametricOctMatrix result = new ParametricOctMatrix(variables.size() * 2);
		for (final TermVariable t : variables) {
			result.addVar(t);
		}

		mUtils.debug(result.getMapping().toString());

		mUtils.debug("Created ParametricOctMatrix of size " + variables.size() * 2);

		for (final OctagonTerm t : terms) {
			if (t instanceof OneVarOctTerm) {
				result.setValue(t.getValue(), t.getFirstVar(), t.isFirstNegative());
			} else if (t instanceof TwoVarOctTerm) {
				result.setValue(t.getValue(), t.getFirstVar(), t.isFirstNegative(), t.getSecondVar(),
						t.isSecondNegative());
			} else {
				throw new UnsupportedOperationException();
			}
		}
		return result;
	}

	private void addValue(ConstantTerm t, boolean negate) {
		BigDecimal value = BigDecimal.ZERO;
		if (t.getValue() instanceof Rational) {
			if (((Rational) t.getValue()).denominator().equals(BigInteger.ONE)) {
				value = new BigDecimal(((Rational) t.getValue()).numerator());
			}
		} else if (t.getValue() instanceof BigDecimal) {
			value = (BigDecimal) t.getValue();
		} else if (t.getValue() instanceof BigInteger) {
			value = new BigDecimal((BigInteger) t.getValue());
		}
		if (negate)
			value = value.negate();
		mValue = mValue.add(value);
	}

	private void addVariable(TermVariable var, boolean negative) {
		if (mFirstVar == null) {
			mFirstVar = var;
			mFirstNegative = negative;
		} else if (mSecondVar == null) {
			mSecondVar = var;
			mSecondNegative = negative;
		} else {
			// Exception
		}
	}

	private void resetTerm() {
		mFirstVar = null;
		mSecondVar = null;
		mFirstCoefficient = null;
		mSecondCoefficient = null;
		mFirstNegative = false;
		mSecondNegative = false;
		mValue = new BigDecimal(0);
	}

	private void transformTerm(Term t, boolean negate) {

		mUtils.debug(("> Walking over neutral Term: " + (negate ? "not: " : "") + t.toString()));

		if (mCheckedTerms.contains(t)) {
			return;
		}

		if (t instanceof ApplicationTerm) {
			final ApplicationTerm aT = (ApplicationTerm) t;
			final String functionName = aT.getFunction().getName();

			mUtils.debug(">> Application of type: " + functionName);

			boolean swap = false;

			if (functionName.compareTo("<") == 0) {
				mType = InequalityType.LESSER;
			} else if (functionName.compareTo(">") == 0) {
				mType = InequalityType.LESSER;
				swap = true;
			} else if (functionName.compareTo("<=") == 0) {
				mType = InequalityType.LESSER_EQUAL;
			} else if (functionName.compareTo(">=") == 0) {
				mType = InequalityType.LESSER_EQUAL;
				swap = true;
			} else if (functionName.compareTo("not") == 0) {
				enqueueWalker(new OctagonTermWalker(aT.getParameters()[0], true));
				return;
			} else if (functionName.compareTo("=") == 0) {
				mUtils.debug(">> EQUALITY");
				final Term first = mManagedScript.getScript().term("<=", aT.getParameters()[0], aT.getParameters()[1]);
				final Term second = mManagedScript.getScript().term("<=", aT.getParameters()[1], aT.getParameters()[0]);

				enqueueWalker(new OctagonTermWalker(first, false));
				mAdditionalTerms.add(second);
				return;
			} else {

			}

			if (negate) {
				if (mType.equals(InequalityType.LESSER)) {
					mType = InequalityType.LESSER_EQUAL;
				} else {
					mType = InequalityType.LESSER;
				}
				swap = !swap;
			}

			final Term leftSide = (swap ? aT.getParameters()[0] : aT.getParameters()[1]);
			final Term rightSide = (swap ? aT.getParameters()[1] : aT.getParameters()[0]);

			enqueueWalker(new OctagonTermWalker(leftSide, InequalitySide.LEFT));
			enqueueWalker(new OctagonTermWalker(rightSide, InequalitySide.RIGHT));

			return;

		} else if (t instanceof AnnotatedTerm) {
			enqueueWalker(new OctagonTermWalker(((AnnotatedTerm) t).getSubterm(), InequalitySide.NONE));

			return;

		}
	}

	private void transformTermSide(Term t, InequalitySide side, boolean negate) {

		mUtils.debug("> Walking over " + side + " Term: " + t.toString());
		mUtils.debug("Type: " + t.getClass().toString());

		if (t instanceof ApplicationTerm) {
			final ApplicationTerm aT = (ApplicationTerm) t;
			final String functionName = aT.getFunction().getName();

			mUtils.debug(">> Application of type: " + functionName);

			if (functionName.compareTo("-") == 0) {
				if (aT.getParameters().length == 1) {
					// Minus with one argument: negate
					enqueueWalker(new OctagonTermWalker(aT.getParameters()[0], side, !negate));
				} else if (aT.getParameters().length == 2) {
					// Minus with two arguments: negate second argument
					enqueueWalker(new OctagonTermWalker(aT.getParameters()[0], side, negate));
					enqueueWalker(new OctagonTermWalker(aT.getParameters()[1], side, !negate));
				}
			} else if (functionName.compareTo("+") == 0) {
				// Plus: default case.
				for (final Term arg : aT.getParameters()) {
					enqueueWalker(new OctagonTermWalker(arg, side, negate));
				}
			} else if (functionName.compareTo("*") == 0) {
				// WHAT NOW - SHOULD NOT HAPPEN M8
			}

			return;

		} else if (t instanceof TermVariable) {

			mUtils.debug(">> Variable");

			if (side == InequalitySide.LEFT) {
				addVariable((TermVariable) t, negate);
			} else {
				addVariable((TermVariable) t, !negate);
			}

			return;

		} else if (t instanceof ConstantTerm) {

			mUtils.debug(">> Constant");

			if (side == InequalitySide.RIGHT) {
				addValue((ConstantTerm) t, negate);
			} else {
				addValue((ConstantTerm) t, !negate);
			}

			return;

		} else if (t instanceof AnnotatedTerm) {
			enqueueWalker(new OctagonTermWalker(((AnnotatedTerm) t).getSubterm(), side));
			return;
		}
	}

}
