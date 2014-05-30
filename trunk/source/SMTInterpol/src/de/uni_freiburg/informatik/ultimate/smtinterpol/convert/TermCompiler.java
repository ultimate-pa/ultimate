/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.util.UnifyHash;

/**
 * Build a representation of the formula where only not, or, ite and =/2 are
 * present.  Linear arithmetic terms are converted into SMTAffineTerms.  We
 * normalize quantifiers to universal quantifiers.  Additionally, this term
 * transformer removes all annotations from the formula.
 * @author Jochen Hoenicke, Juergen Christ
 */
public class TermCompiler extends TermTransformer {
	
	private boolean mBy0Seen = false;
	private Map<Term, Set<String>> mNames;
	
	private IProofTracker mTracker;
	private Utils mUtils;
	private final FormulaUnLet mUnletter = new FormulaUnLet();
	private final UnifyHash<SMTAffineTerm> mAffineUnifier
		= new UnifyHash<SMTAffineTerm>();
	
	public void setProofTracker(IProofTracker tracker) {
		mTracker = tracker;
		mUtils = new Utils(tracker);
	}
	
	public void setAssignmentProduction(boolean on) {
		if (on) {
			mNames = new HashMap<Term, Set<String>>();
		} else
			mNames = null;
	}
	
	public Map<Term, Set<String>> getNames() {
		return mNames;
	}
	
	public void convert(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			FunctionSymbol fsym = appTerm.getFunction();
			if (fsym.isModelValue())
				throw new SMTLIBException("Model values not allowed in input");
			Term[] params = appTerm.getParameters();
			if (fsym.isLeftAssoc() && params.length > 2) {
				Theory theory = appTerm.getTheory();
				if (fsym == theory.mAnd || fsym == theory.mOr) {
					// We keep n-ary and/or
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
//				m_Tracker.expand(appTerm);
				enqueueWalker(new RewriteAdder(appTerm, null));
				BuildApplicationTerm dummy = new BuildApplicationTerm(
				        theory.term(fsym, params[0], params[1]));
				for (int i = params.length - 1; i > 0; i--) {
					enqueueWalker(dummy);
					pushTerm(params[i]);
				}
				pushTerm(params[0]);
				return;
			}
			if (fsym.isRightAssoc() && params.length > 2) {
				Theory theory = appTerm.getTheory();
				if (fsym == theory.mImplies) {
					// We keep n-ary implies
					enqueueWalker(new BuildApplicationTerm(appTerm));
					pushTerms(params);
					return;
				}
//				m_Tracker.expand(appTerm);
				enqueueWalker(new RewriteAdder(appTerm, null));
				BuildApplicationTerm dummy = new BuildApplicationTerm(
				        theory.term(fsym, params[params.length - 2], 
							params[params.length - 1]));
				for (int i = params.length - 1; i > 0; i--)
					enqueueWalker(dummy);
				pushTerms(params);
				return;
			}
			if (fsym.isChainable() && params.length > 2 
					&& !fsym.getName().equals("=")) {
//				m_Tracker.expand(appTerm);
				enqueueWalker(new RewriteAdder(appTerm, null));
				Theory theory = appTerm.getTheory();
				BuildApplicationTerm and = new BuildApplicationTerm(
				        theory.term("and", theory.mTrue, theory.mTrue));
				BuildApplicationTerm dummy = new BuildApplicationTerm(
						theory.term(fsym, params[0], params[1]));
				for (int i = params.length - 1; i > 1; i--) {
					enqueueWalker(and);
					enqueueWalker(dummy);
					pushTerm(params[i]);
					pushTerm(params[i - 1]);
				}
				enqueueWalker(dummy);
				pushTerm(params[1]);
				pushTerm(params[0]);
				return;
			}
		} else if (term instanceof ConstantTerm) {
			SMTAffineTerm res = SMTAffineTerm.create(term);
			mTracker.normalized((ConstantTerm) term, res);
			setResult(res);
			return;
		}
		super.convert(term);
	}
	
	/**
	 * Add the rewrite that expands a function definition to the beginning
	 * of the rewrite list.  Since this definition must come before the 
	 * definition used inside, we use a Walker to add the definition after
	 * we transformed the expanded term.
	 */
	private static class RewriteAdder implements Walker {
		private final ApplicationTerm mAppTerm;
		private final Term mExpanded;
		
		public RewriteAdder(ApplicationTerm term, Term expanded) {
			mAppTerm = term;
			mExpanded = expanded;
		}
		
		public void walk(NonRecursive engine) {
			TermCompiler transformer = (TermCompiler) engine;
			if (mExpanded == null)
				transformer.mTracker.expand(mAppTerm);
			else
				transformer.mTracker.expandDef(mAppTerm, mExpanded);
		}

		public String toString() {
			return "addrewrite " + mAppTerm.getFunction().getApplicationString();
		}
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] args) {
		FunctionSymbol fsym = appTerm.getFunction();
		Theory theory = appTerm.getTheory();
		
 		if (fsym.getDefinition() != null) {
			Term definition = theory.let(
					fsym.getDefinitionVars(), appTerm.getParameters(), 
					fsym.getDefinition());
			Term expanded = mUnletter.unlet(definition);
			enqueueWalker(new RewriteAdder(appTerm, expanded));
			pushTerm(expanded);
			return;
		}
 		
		Sort[] paramSorts = fsym.getParameterSorts();
		Term[] origArgs = null;
		if (theory.getLogic().isIRA()
			&& paramSorts.length == 2 
			&& paramSorts[0].getName().equals("Real") 
			&& paramSorts[1] == paramSorts[0]) {
			// IRA-Hack
			if (args == appTerm.getParameters())
				args = args.clone();				
			for (int i = 0; i < args.length; i++) {
				if (args[i].getSort().getName().equals("Int")) {
					if (origArgs == null)
						origArgs = mTracker.prepareIRAHack(args);
					args[i] = SMTAffineTerm.create(args[i])
						.toReal(paramSorts[0]);
				}
			}
		}
		
//		for (int i = 0; i < args.length; ++i) {
//			if (args[i] instanceof SMTAffineTerm) {
//				args[i] = ((SMTAffineTerm) args[i]).normalize(this);
//			}
//		}
		if (origArgs != null)
			mTracker.desugar(appTerm, origArgs, args);
		
		if (fsym.isIntern()) {
			if (fsym == theory.mNot) {
				setResult(mUtils.createNot(args[0]));
				return;
			}
			if (fsym == theory.mAnd) {
				setResult(mUtils.createAnd(args));
				return;
			}
			if (fsym == theory.mOr) {
				setResult(mUtils.createOr(args));
				return;
			}
			if (fsym == theory.mXor) {
				mTracker.removeConnective(args,
						null, ProofConstants.RW_XOR_TO_DISTINCT);
				setResult(mUtils.createDistinct(args));
				return;
			}
			if (fsym == theory.mImplies) {
				mTracker.removeConnective(
						args, null, ProofConstants.RW_IMP_TO_OR);
				Term[] tmp = new Term[args.length];
				// We move the conclusion in front (see Simplify tech report)
				for (int i = 1; i < args.length; ++i)
					tmp[i] = mUtils.createNot(args[i - 1]);
				tmp[0] = args[args.length - 1];
				setResult(mUtils.createOr(tmp));
				return;
			}
			if (fsym.getName().equals("ite")) {
				setResult(mUtils.createIte(args[0], args[1], args[2]));
				return;
			}
			if (fsym.getName().equals("=")) {
				setResult(mUtils.createEq(args));
				return;
			}
			if (fsym.getName().equals("distinct")) {
				setResult(mUtils.createDistinct(args));
				return;
			}
			if (fsym.getName().equals("<=")) {
				Term res = SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1]))
						.normalize(this);
				mTracker.removeConnective(
						args, res, ProofConstants.RW_LEQ_TO_LEQ0);
				setResult(mUtils.createLeq0(res));
				return;
			}
			if (fsym.getName().equals(">=")) {
				Term res = SMTAffineTerm.create(args[1])
						.add(SMTAffineTerm.create(Rational.MONE, args[0]))
						.normalize(this);
				mTracker.removeConnective(
						args, res, ProofConstants.RW_GEQ_TO_LEQ0);
				setResult(mUtils.createLeq0(res));
				return;
			}
			if (fsym.getName().equals(">")) {
				Term res = SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1]))
						.normalize(this);
				mTracker.removeConnective(
						args, res, ProofConstants.RW_GT_TO_LEQ0);
				setResult(mUtils.createNot(mUtils.createLeq0(res)));
				return;
			}
			if (fsym.getName().equals("<")) {
				Term res = SMTAffineTerm.create(args[1])
						.add(SMTAffineTerm.create(Rational.MONE, args[0]))
						.normalize(this);
				mTracker.removeConnective(
						args, res, ProofConstants.RW_LT_TO_LEQ0);
				setResult(mUtils.createNot(mUtils.createLeq0(res)));
				return;
			}
			if (fsym.getName().equals("+")) {
				Term res = SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(args[1]))
						.normalize(this);
				mTracker.sum(fsym, args, res);
				setResult(res);
				return;
			} else if (fsym.getName().equals("-") && paramSorts.length == 2) {
				Term res = SMTAffineTerm.create(args[0])
						.add(SMTAffineTerm.create(Rational.MONE, args[1]))
						.normalize(this);
				mTracker.sum(fsym, args, res);
				setResult(res);
				return;
			} else if (fsym.getName().equals("*")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				SMTAffineTerm res;
				if (arg0.isConstant())
					res = arg1.mul(arg0.getConstant());
				else if (arg1.isConstant())
					res = arg0.mul(arg1.getConstant());
				else
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				Term result = res.normalize(this);
				mTracker.sum(fsym, args, result);
				setResult(result);
				return;
			} else if (fsym.getName().equals("/")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				if (arg1.isConstant()) {
					if (arg1.getConstant().equals(Rational.ZERO)) {
						mBy0Seen = true;
						setResult(theory.term("@/0", arg0));
					} else {
						Term res = arg0.mul(arg1.getConstant().inverse())
								.normalize(this);
						mTracker.sum(fsym, args, res);
						setResult(res);
					}
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("div")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				Term narg0 = arg0.normalize(this);
				Term narg1 = arg1.normalize(this);
				Rational divisor = arg1.getConstant();
				if (arg1.isConstant() && divisor.isIntegral()) {
					if (divisor.equals(Rational.ZERO)) {
						mBy0Seen = true;
						setResult(theory.term("@div0", narg0));
					} else if (divisor.equals(Rational.ONE)) {
						mTracker.div(narg0, narg1, narg0,
								ProofConstants.RW_DIV_ONE);
						setResult(narg0);
					} else if (divisor.equals(Rational.MONE)) {
						Term res = arg0.negate().normalize(this);
						mTracker.div(narg0, narg1, res,
								ProofConstants.RW_DIV_MONE);
						setResult(res);
					} else if (arg0.isConstant()) {
						// We have (div c0 c1) ==> constDiv(c0, c1)
						Rational div = constDiv(arg0.getConstant(),
								arg1.getConstant());
						Term res = SMTAffineTerm.create(
								div.toTerm(arg0.getSort())).normalize(this);
						mTracker.div(narg0, narg1, res,
								ProofConstants.RW_DIV_CONST);
						setResult(res);
					} else {
						setResult(theory.term(fsym, narg0, narg1));
					}
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("mod")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(args[1]);
				Term narg0 = arg0.normalize(this);
				Term narg1 = arg1.normalize(this);
				Rational divisor = arg1.getConstant();
				if (arg1.isConstant() && divisor.isIntegral()) {
					if (divisor.equals(Rational.ZERO)) {
						mBy0Seen = true;
						setResult(theory.term("@mod0", narg0));
					} else if (divisor.equals(Rational.ONE)) {
						// (mod x 1) == 0
						Term res = SMTAffineTerm.create(
								Rational.ZERO.toTerm(arg0.getSort()))
								.normalize(this);
						mTracker.mod(narg0, narg1, res,
								ProofConstants.RW_MODULO_ONE);
						setResult(res);
					} else if (divisor.equals(Rational.MONE)) {
						// (mod x -1) == 0
						Term res = SMTAffineTerm.create(
								Rational.ZERO.toTerm(arg0.getSort()))
								.normalize(this);
						mTracker.mod(arg0, arg1, res,
								ProofConstants.RW_MODULO_MONE);
						setResult(res);
					} else if (arg0.isConstant()) {
						// We have (mod c0 c1) ==> c0 - c1 * constDiv(c0, c1)
						Rational c0 = arg0.getConstant();
						Rational c1 = arg1.getConstant();
						Rational mod = c0.sub(constDiv(c0, c1).mul(c1));
						Term res = SMTAffineTerm.create(
								mod.toTerm(arg0.getSort())).normalize(this);
						mTracker.mod(arg0, arg1, res,
								ProofConstants.RW_MODULO_CONST);
						setResult(res);
					} else {
						SMTAffineTerm ydiv =
								SMTAffineTerm.create(theory.term(
										"div", arg0, arg1)).
										mul(arg1.getConstant());
						Term res = arg0.add(ydiv.negate()).normalize(this);
						setResult(res);
						mTracker.modulo(appTerm, res);
					}
					return;
				} else {
					throw new UnsupportedOperationException("Unsupported non-linear arithmetic");
				}
			} else if (fsym.getName().equals("-") && paramSorts.length == 1) {
				Term res = SMTAffineTerm.create(args[0]).negate()
						.normalize(this);
				mTracker.sum(fsym, args, res);
				setResult(res);
				return;
			} else if (fsym.getName().equals("to_real")) {
				SMTAffineTerm arg = SMTAffineTerm.create(args[0]);
				Term res = arg.toReal(fsym.getReturnSort()).normalize(this);
				setResult(res);
				if (arg.isConstant())
					mTracker.toReal(arg, res);
				return;
			} else if (fsym.getName().equals("to_int")) {
				// We don't convert to_int here but defer it to the clausifier
				// But we simplify it here...
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				if (arg0.isConstant()) {
					Term res = SMTAffineTerm.create(
							arg0.getConstant().floor().toTerm(
									fsym.getReturnSort())).normalize(this);
					mTracker.toInt(arg0, res);
					setResult(res);
					return;
				}
			}  else if (fsym.getName().equals("divisible")) {
				SMTAffineTerm arg0 = SMTAffineTerm.create(args[0]);
				SMTAffineTerm arg1 = SMTAffineTerm.create(
						Rational.valueOf(fsym.getIndices()[0], BigInteger.ONE),
						arg0.getSort());
				Term res;
				if (arg1.getConstant().equals(Rational.ONE))
					res = theory.mTrue;
				else if (arg0.isConstant()) {
					Rational c0 = arg0.getConstant();
					Rational c1 = arg1.getConstant();
					Rational mod = c0.sub(constDiv(c0, c1).mul(c1));
					res = mod.equals(Rational.ZERO) ? theory.mTrue : theory.mFalse;
				} else
					res = theory.term("=", arg0, SMTAffineTerm.create(
						theory.term("div", arg0, arg1)).mul(arg1.getConstant())
						.normalize(this));
				setResult(res);
				mTracker.divisible(appTerm.getFunction(), arg0, res);
				return;
			} else if (fsym.getName().equals("store")) {
				Term array = args[0];
				Term idx = args[1];
				Term nestedIdx = getArrayStoreIdx(array);
				if (nestedIdx != null) {
					// Check for store-over-store
					SMTAffineTerm diff = SMTAffineTerm.create(idx).add(
							SMTAffineTerm.create(nestedIdx).negate());
					if (diff.isConstant() && diff.getConstant().equals(
					        Rational.ZERO)) {
						// Found store-over-store => ignore inner store
						ApplicationTerm appArray = (ApplicationTerm) array;
						Term result = theory.term(fsym,
								appArray.getParameters()[0], args[1], args[2]);
						mTracker.arrayRewrite(args, result,
								ProofConstants.RW_STORE_OVER_STORE);
						setResult(result);
						return;
					}
				}
			} else if (fsym.getName().equals("select")) {
				Term array = args[0];
				Term idx = args[1];
				Term nestedIdx = getArrayStoreIdx(array);
				if (nestedIdx != null) {
					// Check for select-over-store
					SMTAffineTerm diff = SMTAffineTerm.create(idx).add(
							SMTAffineTerm.create(nestedIdx).negate());
					if (diff.isConstant()) { 
						// Found select-over-store
						ApplicationTerm appArray = (ApplicationTerm) array;
						if (diff.getConstant().equals(Rational.ZERO)) {
							// => transform into value
							Term result = appArray.getParameters()[2];
							mTracker.arrayRewrite(args, result,
									ProofConstants.RW_SELECT_OVER_STORE);
							setResult(result);
							return;
						} else { // Both indices are numerical and distinct.
							// => transform into (select a idx)
							Term result = theory.term("select",
									appArray.getParameters()[0], idx);
							mTracker.arrayRewrite(args, result,
									ProofConstants.RW_SELECT_OVER_STORE);
							setResult(result);
							return;
						}
					}
				}
			} else if (fsym.getName().equals("@undefined"))
				throw new SMTLIBException("Undefined value in input");
		}
		// not an intern function symbols
		super.convertApplicationTerm(appTerm, args);
	}
	
	public final static Rational constDiv(Rational c0, Rational c1) {
		Rational div = c0.div(c1);
		return c1.isNegative() ? div.ceil() : div.floor();
	}
	
	private final static Term getArrayStoreIdx(Term array) {
		if (array instanceof ApplicationTerm) {
			ApplicationTerm appArray = (ApplicationTerm) array;
			FunctionSymbol arrayFunc = appArray.getFunction();
			if (arrayFunc.isIntern() &&	arrayFunc.getName().equals("store"))
				// (store a i v)
				return appArray.getParameters()[1];
		}
		return null;
	}

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		if (old.getQuantifier() == QuantifiedFormula.EXISTS)
			super.postConvertQuantifier(old, newBody);
		else {
			// We should create (forall (x) (newBody x))
			// This becomes (not (exists (x) (not (newBody x))))
			Term negNewBody = mUtils.createNot(newBody);
			Theory t = old.getTheory();
			Term res = t.term(t.mNot,
					t.exists(old.getVariables(), negNewBody));
			setResult(res);
		}
	}

	@Override
	public void postConvertAnnotation(AnnotatedTerm old,
			Annotation[] newAnnots, Term newBody) {
		if (mNames != null
		        && newBody.getSort() == newBody.getTheory().getBooleanSort()) {
			Annotation[] oldAnnots = old.getAnnotations();
			for (Annotation annot : oldAnnots) {
				if (annot.getKey().equals(":named")) {
					Set<String> oldNames = mNames.get(newBody);
					if (oldNames == null) {
						oldNames = new HashSet<String>();
						mNames.put(newBody, oldNames);
					}
					oldNames.add(annot.getValue().toString());
				}
			}
		}
		mTracker.strip(old);
		setResult(newBody);
	}
	/**
	 * Get and reset the division-by-0 seen flag.
	 * @return The old division-by-0 seen flag.
	 */
	public boolean resetBy0Seen() {
		boolean old = mBy0Seen;
		mBy0Seen = false;
		return old;
	}
	
	public SMTAffineTerm unify(SMTAffineTerm affine) {
		return mAffineUnifier.unify(affine);
	}
}
