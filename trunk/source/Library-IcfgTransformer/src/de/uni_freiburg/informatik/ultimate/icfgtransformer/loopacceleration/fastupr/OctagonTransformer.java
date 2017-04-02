package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonConcatination;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonTerm;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OneVarOctTerm;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.ParametricOctMatrix;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.TwoVarOctTerm;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class OctagonTransformer extends NonRecursive {
	
	private final ILogger mLogger;
	private final HashSet<Term> mCheckedTerms;
	private TermVariable mFirstVar;
	private boolean mFirstNegative;
	private BigDecimal mFirstCoefficient;
	private TermVariable mSecondVar;
	private boolean mSecondNegative;
	private BigDecimal mSecondCoefficient;
	private BigDecimal mValue;
	private InequalityType mType;
	
	private ParametricOctMatrix mOct;
	
	public OctagonTransformer(ILogger logger) {
		mLogger = logger;
		mCheckedTerms = new HashSet<>();
		mValue = new BigDecimal(0);
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
	
	public OctagonConcatination transform(ArrayList<Term> terms) {
		mLogger.debug("Starting Term to OctagonTransformation");
		mOct = new ParametricOctMatrix();
		
		OctagonConcatination octagon = new OctagonConcatination();
		
		for (Term t : terms) {
			mLogger.debug("Getting Value from:" + t.toString());
			resetTerm();
			run(new OctagonTermWalker(t, InequalitySide.NONE));
			
			
			if(mType == InequalityType.LESSER) mValue = mValue.subtract(new BigDecimal(1));
			mLogger.debug("Value is:" + mValue.toString());
			
			
			if(mFirstVar == null) {
				mLogger.debug("ERROR");
			} else if (mSecondVar == null) {
				mValue = mValue.multiply(new BigDecimal(2));
				octagon.addTerm((OctagonTerm) new OneVarOctTerm(mValue, mFirstVar, mFirstNegative));
			} else {
				octagon.addTerm(new TwoVarOctTerm(mValue, mFirstVar, mFirstNegative, mSecondVar, mSecondNegative));
			}
		}
		
		mLogger.debug("Octagon:");
		mLogger.debug(octagon.toString());
		
		return octagon;
	}
	
	private static class OctagonTermWalker implements NonRecursive.Walker {

		private final Term mTerm;
		private InequalitySide mSide;
		private final boolean mNegate;
		
		OctagonTermWalker(Term t, InequalitySide side) {
			this(t, side, false);
		}
		
		OctagonTermWalker(Term t, InequalitySide side, boolean negate) {
			mTerm = t;
			mSide = side;
			mNegate = negate;
		}
		
		@Override
		public void walk(NonRecursive engine) {
			// TODO Auto-generated method stub
			if(mSide == InequalitySide.NONE) {
				((OctagonTransformer) engine).transformTerm(mTerm);
			} else {
				((OctagonTransformer) engine).transformTermSide(mTerm, mSide, mNegate);
			} 
		} 
		
	}
	
	
	
	private void transformTerm(Term t) {
		
		mLogger.debug("> Walking over neutral Term: " + t.toString());
		
		if(mCheckedTerms.contains(t)) {
			return;
		}
		
		if(t instanceof ApplicationTerm) {
			ApplicationTerm aT = (ApplicationTerm) t;
			String functionName = aT.getFunction().getName();
			
			mLogger.debug(">> Application of type: " + functionName);
			
			boolean swap = false;
			
			if(functionName.compareTo("<") == 0) {
				mType = InequalityType.LESSER;
			} else if (functionName.compareTo(">") == 0) {
				mType = InequalityType.LESSER;
				swap = true;
			} else if (functionName.compareTo("<=") == 0) {
				mType = InequalityType.LESSER_EQUAL;
			} else if (functionName.compareTo(">=") == 0) {
				mType = InequalityType.LESSER_EQUAL;
				swap = true;
			} else {
				// throw exception
			}
			
			Term leftSide = (swap ? aT.getParameters()[0] : aT.getParameters()[1]);
			Term rightSide = (swap ? aT.getParameters()[1] : aT.getParameters()[0]);
			
			enqueueWalker(new OctagonTermWalker(leftSide, InequalitySide.LEFT));
			enqueueWalker(new OctagonTermWalker(rightSide, InequalitySide.RIGHT));
			
			return;
			
		} else if (t instanceof AnnotatedTerm) {
			enqueueWalker(new OctagonTermWalker(((AnnotatedTerm) t).getSubterm(),
					InequalitySide.NONE));
			
			return;
			
		}
	}


	private void transformTermSide(Term t, InequalitySide side, boolean negate) {
		
		mLogger.debug("> Walking over " + side + " Term: " + t.toString());
		
		if (t instanceof ApplicationTerm) {
			ApplicationTerm aT = (ApplicationTerm) t;
			String functionName = aT.getFunction().getName();
			
			mLogger.debug(">> Application of type: " + functionName);
			
			if(functionName.compareTo("-") == 0) {
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
				for (Term arg : aT.getParameters()) {
					enqueueWalker(new OctagonTermWalker(arg, side, negate));
				}
			} else if (functionName.compareTo("*") == 0) {
				// WHAT NOW - SHOULD NOT HAPPEN M8
			}
			
			return;
			
		} else if (t instanceof TermVariable) {
			
			mLogger.debug(">> Variable");
			
			if (side == InequalitySide.LEFT) {
				addVariable((TermVariable) t, negate);
			} else {
				addVariable((TermVariable) t, !negate);
			}
			
			return;
			
		} else if (t instanceof ConstantTerm) {
			
			mLogger.debug(">> Constant");
			
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
	

	private void addValue(ConstantTerm t, boolean negate) {
		BigDecimal value = BigDecimal.ZERO;
		if(t.getValue() instanceof Rational) {
			if (((Rational) t.getValue()).denominator().equals(BigInteger.ONE)) {
				value = new BigDecimal(((Rational) t.getValue()).numerator());
			}
		} else if (t.getValue() instanceof BigDecimal) {
			value = (BigDecimal) t.getValue();
		} else if (t.getValue() instanceof BigInteger) {
			value = new BigDecimal ((BigInteger) t.getValue());
		}
		if (negate) value.negate();
		mValue = mValue.add(value);
	}

	private enum InequalityType {
		NONE,
		LESSER,
		LESSER_EQUAL,
	}

	private enum InequalitySide {
		NONE,
		LEFT,
		RIGHT
	}
	
	
}
