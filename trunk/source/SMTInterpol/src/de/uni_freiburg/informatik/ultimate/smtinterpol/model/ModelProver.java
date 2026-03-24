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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.math.BigInteger;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.BitvectorRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.DataTypeRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofRules;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Create a model proof. A model proof shows that a given formula holds under
 * the current model.
 *
 * The term transformer creates a proof for @code{(= t eval(t))} annotated
 * with @code{eval(t)}.
 *
 * @author Jochen Hoenicke
 */
public class ModelProver extends TermTransformer {

	/**
	 * A helper to enqueue either the true or the false branch of an ite.
	 *
	 * @author Jochen Hoenicke
	 */
	private static class ITESelector implements Walker {

		private final ApplicationTerm mIte;

		public ITESelector(final ApplicationTerm ite) {
			mIte = ite;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ModelProver eval = (ModelProver) engine;
			eval.postConvertIte(mIte, eval.getConverted());
		}
	}

	/**
	 * A helper to process a transitivity step and apply it to the proof.
	 *
	 * @author Jochen Hoenicke
	 */
	private static class TransitivityStep implements Walker {

		/** The original term that was evaluated. */
		private final Term mOrigTerm;
		/** The term to which the original term was rewritten before being evaluated. */
		private final Term mMidTerm;
		/** The proof of `(= mOrigTerm mMidTerm)`. */
		private final Term mProof;

		public TransitivityStep(final Term origTerm, final Term midTerm, final Term proof) {
			mOrigTerm = origTerm;
			mMidTerm = midTerm;
			mProof = proof;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ModelProver eval = (ModelProver) engine;
			eval.postTransitivity(mOrigTerm, mMidTerm, mProof, eval.getConverted());
		}
	}

	/**
	 * The model where to evaluate in.
	 */
	private final Model mModel;

	private final ProofRules mProofRules;
	private final ProofUtils mProofUtils;
	private final FormulaUnLet mUnletter;

	/**
	 * The scoped let map. Each scope corresponds to a partially executed let or a
	 * quantifier on the todo stack. It gives the mapping for each term variable
	 * defined in that scope to the corresponding term.
	 */
	private final ScopedHashMap<TermVariable, Term> mLetMap = new ScopedHashMap<>(false);

	private static boolean isBooleanValue(final Term term) {
		final Theory theory = term.getTheory();
		return term == theory.mTrue || term == theory.mFalse;
	}

	private Term annotateProof(Term proof, Term resultTerm) {
		final Theory theory = proof.getTheory();
		return theory.annotatedTerm(new Annotation[] { new Annotation(":term", resultTerm) }, proof);
	}

	private Term getAnnotation(Term annotatedProof) {
		return (Term) ((AnnotatedTerm) annotatedProof).getAnnotations()[0].getValue();
	}

	private Term getProof(Term annotatedProof) {
		return ((AnnotatedTerm) annotatedProof).getSubterm();
	}

	private void enqueueTransitivityStep(Term origTerm, Term midTerm, Term proofEq) {
		enqueueWalker(new TransitivityStep(origTerm, midTerm, proofEq));
	}

	@Override
	public void convert(Term term) {
		while (term instanceof AnnotatedTerm) {
			final Term subTerm = ((AnnotatedTerm) term).getSubterm();
			enqueueTransitivityStep(term, subTerm, mProofRules.delAnnot(term));
			term = subTerm;
		}
		if (term instanceof ConstantTerm) {
			if (term.getSort().isNumericSort()) {
				final Term result = SMTAffineTerm.convertConstant((ConstantTerm) term).toTerm(term.getSort());
				final Term proofEq = mProofUtils.proveConstEquality(term, result);
				final Term resultWithProof = annotateProof(proofEq, result);
				setResult(resultWithProof);
				return;
			} else if (term.getSort().isBitVecSort()) {
				final Object value = ((ConstantTerm) term).getValue();
				if (value instanceof String) {
					BigInteger result;
					final String bitString = (String) value;
					if (bitString.startsWith("#b")) {
						result = new BigInteger(bitString.substring(2), 2);
					} else {
						assert bitString.startsWith("#x");
						result = new BigInteger(bitString.substring(2), 16);
					}
					final Term bvTerm = createBitvectorTerm(result, term.getSort());
					final BigInteger bitLength = new BigInteger(term.getSort().getIndices()[0]);
					setResult(annotateProof(mProofRules.bvConst(result, bitLength), bvTerm));
				} else {
					assert value instanceof BigInteger;
					setResult(annotateProof(mProofRules.refl(term), term));
				}
				return;
			}
			throw new InternalError("Don't know how to evaluate this: " + term);
		}
		if (term instanceof TermVariable) {
			if (mLetMap.containsKey(term)) {
				setResult(mLetMap.get(term));
				return;
			}
			throw new SMTLIBException("Terms to evaluate must be closed");
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fs = appTerm.getFunction();
			if (fs.isIntern()) {
				final Theory theory = appTerm.getTheory();
				final Term[] appParams = appTerm.getParameters();
				switch (fs.getName()) {
				case SMTLIBConstants.ITE:
					enqueueWalker(new ITESelector(appTerm));
					pushTerm(appParams[0]);
					return;

				case SMTLIBConstants.EQUALS:
					if (fs.getDefinition() != null) {
						// LIRA equals is expanded before evaluating, to evaluate the toReal
						// arguments.
						final Term expanded = mUnletter
								.unlet(appTerm.getTheory().let(fs.getDefinitionVars(), appParams, fs.getDefinition()));
						enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
						pushTerm(expanded);
						return;
					}
					break;

				case SMTLIBConstants.MINUS:
				case SMTLIBConstants.DIVIDE:
				case SMTLIBConstants.DIV:
					if (appParams.length > 2) {
						// non-binary left-associative operators are expanded before evaluating.
						// to handle division by 0 and simplify the proofs.
						Term expanded = appParams[0];
						for (int i = 1; i < appParams.length; i++) {
							expanded = theory.term(appTerm.getFunction(), expanded, appParams[1]);
						}
						enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
						pushTerm(expanded);
						return;
					}
					break;

				case SMTLIBConstants.LEQ:
				case SMTLIBConstants.LT:
				case SMTLIBConstants.GEQ:
				case SMTLIBConstants.GT:
					if (appParams.length > 2) {
						// non-binary chainable comparisons are expanded before evaluating.
						final Term[] pairs = new Term[appParams.length - 1];
						for (int i = 0; i < pairs.length; i++) {
							pairs[i] = theory.term(appTerm.getFunction(), appParams[i], appParams[i + 1]);
						}
						final Term expanded = theory.term(SMTLIBConstants.AND, pairs);
						enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
						pushTerm(expanded);
						return;
					}
					// binary geq/gt is rewritten to leq/lt.
					if (fs.getName() == SMTLIBConstants.GT) {
						final Term expanded = theory.term(SMTLIBConstants.LT, appParams[1], appParams[0]);
						enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
						pushTerm(expanded);
						return;
					}
					if (fs.getName() == SMTLIBConstants.GEQ) {
						final Term expanded = theory.term(SMTLIBConstants.LEQ, appParams[1], appParams[0]);
						enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
						pushTerm(expanded);
						return;
					}
					break;

				case SMTLIBConstants.IS_INT: {
					// we expand IS_INT; TODO, this should be a is-int-def proof rule, not expand.
					final Term expanded = mUnletter
							.unlet(appTerm.getTheory().let(fs.getDefinitionVars(), appParams, fs.getDefinition()));
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}

				// expand most of the bit-vector operations
				case SMTLIBConstants.BVADD: {
					final Term expanded = BitvectorRules.expandBvAdd(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVSUB: {
					final Term expanded = BitvectorRules.expandBvSub(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVMUL: {
					final Term expanded = BitvectorRules.expandBvMul(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVNEG: {
					assert appParams.length == 1;
					final Term expanded = BitvectorRules.expandBvNeg(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVNEGO: {
					final Term expanded = BitvectorRules.expandBvNegO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVUADDO: {
					final Term expanded = BitvectorRules.expandBvUAddO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVSADDO: {
					final Term expanded = BitvectorRules.expandBvSAddO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVUMULO: {
					final Term expanded = BitvectorRules.expandBvUMulO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVSMULO: {
					final Term expanded = BitvectorRules.expandBvSMulO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVSDIVO: {
					final Term expanded = BitvectorRules.expandBvSDivO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVUSUBO: {
					final Term expanded = BitvectorRules.expandBvUSubO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVSSUBO: {
					final Term expanded = BitvectorRules.expandBvSSubO(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVNOT: {
					assert appParams.length == 1;
					final Term expanded = BitvectorRules.expandBvNot(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVAND: {
					assert appParams.length >= 2;
					final Term expanded = BitvectorRules.expandBvAnd(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVOR: {
					assert appParams.length >= 2;
					final Term expanded = BitvectorRules.expandBvOr(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVXOR: {
					assert appParams.length >= 2;
					final Term expanded = BitvectorRules.expandBvXor(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.BVNAND: {
					assert appParams.length == 2;
					final Term expanded = BitvectorRules.expandBvNAnd(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.CONCAT: {
					assert appParams.length >= 2;
					final Term expanded = BitvectorRules.expandConcat(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				case SMTLIBConstants.EXTRACT: {
					assert appParams.length == 1;
					final Term expanded = BitvectorRules.expandExtract(fs, appParams);
					enqueueTransitivityStep(appTerm, expanded, mProofRules.expand(appTerm));
					pushTerm(expanded);
					return;
				}
				}
			}
		} else if (term instanceof QuantifiedFormula) {
			throw new SMTLIBException("Quantifiers not supported in model proofs");
		} else if (term instanceof MatchTerm) {
			final MatchTerm matchTerm = (MatchTerm) term;
			final Term iteTerm = DataTypeRules.buildIteForMatch(matchTerm);
			enqueueTransitivityStep(matchTerm, iteTerm, mProofRules.dtMatch(matchTerm));
			pushTerm(iteTerm);
			return;
		}
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final Theory theory = appTerm.getTheory();
		final Term[] argTerms = new Term[newArgs.length];
		final Term[] argProofs = new Term[newArgs.length];
		for (int i = 0; i < newArgs.length; i++) {
			argTerms[i] = getAnnotation(newArgs[i]);
			argProofs[i] = getProof(newArgs[i]);
		}
		if (appTerm.getFunction().isIntern()) {
			switch (appTerm.getFunction().getName()) {
			case SMTLIBConstants.TRUE:
			case SMTLIBConstants.FALSE:
			case SMTLIBConstants.NOT:
			case SMTLIBConstants.OR:
			case SMTLIBConstants.AND:
			case SMTLIBConstants.IMPLIES:
			case SMTLIBConstants.EQUALS:
			case SMTLIBConstants.DISTINCT:
				setResult(interpretWithoutCongruence(appTerm, argTerms, argProofs));
				return;
			}
		}

		final Term newTerm = theory.term(appTerm.getFunction(), argTerms);
		if (newTerm != appTerm) {
			Term congProof = mProofRules.cong(appTerm, newTerm);
			for (int i = 0; i < newArgs.length; i++) {
				Term eqProof;
				final Term origTerm = appTerm.getParameters()[i];
				final Term equality = theory.term(SMTLIBConstants.EQUALS, origTerm, argTerms[i]);
				if (origTerm.getSort().getName() == SMTLIBConstants.BOOL) {
					if (argTerms[i] == theory.mTrue) {
						eqProof = mProofUtils.res(origTerm, argProofs[i], mProofRules.iffIntro2(equality));
					} else {
						eqProof = mProofUtils.res(origTerm, mProofRules.iffIntro1(equality), argProofs[i]);
					}
				} else {
					eqProof = argProofs[i];
				}
				congProof = mProofUtils.res(equality, eqProof, congProof);
			}
			enqueueTransitivityStep(appTerm, newTerm, congProof);
		}

		final FunctionSymbol fs = appTerm.getFunction();
		if (fs.isModelValue()) {
			final int idx = Integer.parseInt(fs.getName().substring(1));
			final Term modelVal = mModel.getModelValue(idx, fs.getReturnSort());
			if (modelVal == appTerm) {
				setResult(annotateProof(mProofRules.refl(appTerm), appTerm));
			} else {
				setResult(annotateProof(mProofRules.expand(appTerm), modelVal));
			}
		} else if (fs.isIntern()) {
			final Term result = interpret(appTerm, fs, argTerms);
			if (result != null) {
				setResult(result);
			}
		} else {
			Term expanded;
			if (fs.getDefinition() != null) {
				expanded = mUnletter
						.unlet(appTerm.getTheory().let(fs.getDefinitionVars(), argTerms, fs.getDefinition()));
			} else {
				expanded = lookupFunction(appTerm, argTerms);
			}
			enqueueTransitivityStep(newTerm, expanded, mProofRules.expand(newTerm));
			pushTerm(expanded);
		}
	}

	@Override
	public void preConvertLet(final LetTerm oldLet, final Term[] newValues) {
		mLetMap.beginScope();
		final TermVariable[] vars = oldLet.getVariables();
		for (int i = 0; i < vars.length; i++) {
			mLetMap.put(vars[i], newValues[i]);
		}
		super.preConvertLet(oldLet, newValues);
	}

	public void postConvertIte(ApplicationTerm ite, Term conditionEval) {
		final Term origCondition = ite.getParameters()[0];
		final Term condition = getAnnotation(conditionEval);
		final Term conditionProof = getProof(conditionEval);
		assert isBooleanValue(condition) : "condition must be 'true' or 'false'";
		final boolean isTrue = (condition == condition.getTheory().mTrue);
		final Term branchTerm = ite.getParameters()[isTrue ? 1 : 2];
		final Term proof = isTrue ? mProofUtils.res(origCondition, conditionProof, mProofRules.ite1(ite))
				: mProofUtils.res(origCondition, mProofRules.ite2(ite), conditionProof);
		enqueueTransitivityStep(ite, branchTerm, proof);
		convert(branchTerm);
	}

	public void postTransitivity(Term origTerm, Term midTerm, Term proofEq1, Term converted) {
		final Theory theory = origTerm.getTheory();
		final Term endTerm = getAnnotation(converted);
		final Term proofEq2 = getProof(converted);
		final Term equality1 = theory.term(SMTLIBConstants.EQUALS, origTerm, midTerm);
		Term proof;
		if (endTerm.getSort().isInternal() && endTerm.getSort().getName() == SMTLIBConstants.BOOL) {
			if (endTerm == endTerm.getTheory().mTrue) {
				proof = mProofUtils.res(midTerm, proofEq2,
						mProofUtils.res(equality1, proofEq1, mProofRules.iffElim1(equality1)));
			} else {
				assert endTerm == endTerm.getTheory().mFalse;
				proof = mProofUtils.res(midTerm, mProofUtils.res(equality1, proofEq1, mProofRules.iffElim2(equality1)),
						proofEq2);
			}
		} else {
			if (midTerm == endTerm) {
				proof = proofEq1;
			} else {
				final Term equality2 = theory.term(SMTLIBConstants.EQUALS, midTerm, endTerm);
				proof = mProofUtils.res(equality2, proofEq2,
						mProofUtils.res(equality1, proofEq1, mProofRules.trans(origTerm, midTerm, endTerm)));
			}
		}
		setResult(annotateProof(proof, endTerm));
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		setResult(newBody);
		mLetMap.endScope();
	}

	public ModelProver(final Model model) {
		mModel = model;
		mProofRules = new ProofRules(model.getTheory());
		mProofUtils = new ProofUtils(mProofRules);
		mUnletter = new FormulaUnLet();
	}

	public Term evaluate(final Term input) {
		return transform(input);
	}

	private Term lookupFunction(ApplicationTerm funcTerm, final Term[] args) {
		final FunctionValue val = mModel.getFunctionValue(funcTerm.getFunction());
		final LambdaTerm lambda = val.getDefinition();
		final Term expanded = mUnletter
				.unlet(funcTerm.getTheory().let(lambda.getVariables(), args, lambda.getSubterm()));
		return expanded;
	}

	private void expandFunction(ApplicationTerm funcTerm, final Term[] args) {
		final Term expanded = lookupFunction(funcTerm, args);
		enqueueTransitivityStep(funcTerm, expanded, mProofRules.expand(funcTerm));
		pushTerm(expanded);
	}

	private Term interpretWithoutCongruence(ApplicationTerm origTerm, final Term[] argTerms, final Term[] argProofs) {
		final Theory theory = origTerm.getTheory();
		final Term[] origArgs = origTerm.getParameters();
		switch (origTerm.getFunction().getName()) {
		case SMTLIBConstants.TRUE:
			return annotateProof(mProofRules.trueIntro(), theory.mTrue);

		case SMTLIBConstants.FALSE:
			return annotateProof(mProofRules.falseElim(), theory.mFalse);

		case SMTLIBConstants.AND: {
			Term proof = mProofRules.andIntro(origTerm);
			for (int i = 0; i < argTerms.length; i++) {
				if (argTerms[i] == theory.mFalse) {
					proof = mProofUtils.res(origArgs[i], mProofRules.andElim(i, origTerm), argProofs[i]);
					return annotateProof(proof, theory.mFalse);
				}
				assert argTerms[i] == theory.mTrue;
				proof = mProofUtils.res(origArgs[i], argProofs[i], proof);
			}
			return annotateProof(proof, theory.mTrue);
		}

		case SMTLIBConstants.OR: {
			Term proof = mProofRules.orElim(origTerm);
			for (int i = 0; i < argTerms.length; i++) {
				if (argTerms[i] == theory.mTrue) {
					proof = mProofUtils.res(origArgs[i], argProofs[i], mProofRules.orIntro(i, origTerm));
					return annotateProof(proof, theory.mTrue);
				}
				assert argTerms[i] == theory.mFalse;
				proof = mProofUtils.res(origArgs[i], proof, argProofs[i]);
			}
			return annotateProof(proof, theory.mFalse);
		}

		case SMTLIBConstants.IMPLIES: {
			Term proof = mProofRules.impElim(origTerm);
			final int last = argTerms.length - 1;
			for (int i = 0; i < last; i++) {
				if (argTerms[i] == theory.mFalse) {
					proof = mProofUtils.res(origArgs[i], mProofRules.impIntro(i, origTerm), argProofs[i]);
					return annotateProof(proof, theory.mTrue);
				}
				assert argTerms[i] == theory.mTrue;
				proof = mProofUtils.res(origArgs[i], argProofs[i], proof);
			}
			if (argTerms[last] == theory.mTrue) {
				proof = mProofUtils.res(origArgs[last], argProofs[last], mProofRules.impIntro(last, origTerm));
				return annotateProof(proof, theory.mTrue);
			}
			proof = mProofUtils.res(origArgs[last], proof, argProofs[last]);
			return annotateProof(proof, theory.mFalse);
		}

		case SMTLIBConstants.NOT: {
			assert isBooleanValue(argTerms[0]);
			final Term origArg = origTerm.getParameters()[0];
			if (argTerms[0] == theory.mTrue) {
				final Term proof = mProofUtils.res(origArg, argProofs[0], mProofRules.notElim(origTerm));
				return annotateProof(proof, theory.mFalse);
			} else {
				final Term proof = mProofUtils.res(origArg, mProofRules.notIntro(origTerm), argProofs[0]);
				return annotateProof(proof, theory.mTrue);
			}
		}

		case SMTLIBConstants.EQUALS: {
			Term eqProof;
			if (argTerms.length > 2) {
				eqProof = mProofRules.equalsIntro(origTerm);
			} else {
				eqProof = null;
			}
			for (int i = 1; i < argTerms.length; ++i) {
				if (argTerms[i] != argTerms[0]) {
					Term proof = proveDisequality(origArgs[0], argProofs[0], argTerms[0], argTerms[i], argProofs[i],
							origArgs[i]);
					if (argTerms.length > 2) {
						final Term origEquality = theory.term(SMTLIBConstants.EQUALS, origArgs[0], origArgs[i]);
						proof = mProofUtils.res(origEquality, mProofRules.equalsElim(0, i, origTerm), proof);
					}
					return annotateProof(proof, theory.mFalse);
				}
				final Term proof = proveEquality(origArgs[i - 1], argProofs[i - 1], argTerms[i - 1], argProofs[i],
						origArgs[i]);
				eqProof = mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, origArgs[i - 1], origArgs[i]), proof,
						eqProof);
			}
			return annotateProof(eqProof, theory.mTrue);
		}

		case SMTLIBConstants.DISTINCT: {
			Term distinctProof;
			if (argTerms.length > 2) {
				distinctProof = mProofRules.distinctIntro(origTerm);
			} else {
				distinctProof = null;
			}
			for (int i = 0; i < argTerms.length; i++) {
				for (int j = i + 1; j < argTerms.length; j++) {
					if (argTerms[i] == argTerms[j]) {
						Term proof = proveEquality(origArgs[i], argProofs[i], argTerms[i], argProofs[j], origArgs[j]);
						final Term origEquality = theory.term(SMTLIBConstants.EQUALS, origArgs[i], origArgs[j]);
						if (argTerms.length > 2) {
							proof = mProofUtils.res(origEquality, mProofRules.distinctElim(i, j, origTerm), proof);
						}
						return annotateProof(proof, theory.mFalse);
					}
					final Term proof = proveDisequality(origArgs[i], argProofs[i], argTerms[i], argTerms[j],
							argProofs[j], origArgs[j]);
					distinctProof = mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, origArgs[i], origArgs[j]),
							distinctProof, proof);
				}
			}
			return annotateProof(distinctProof, theory.mTrue);
		}
		}
		throw new AssertionError("Unsupported Function");
	}

	private Term proveDisequality(Term ot1, Term eq1, Term ct1, Term ct2, Term eq2, Term ot2) {
		final Theory theory = ot1.getTheory();
		final Term destEq = theory.term(SMTLIBConstants.EQUALS, ot1, ot2);
		if (ct1.getSort() == theory.getBooleanSort()) {
			if (ct1 == theory.mTrue) {
				// ct1 = true, ct2 = false
				return mProofUtils.res(ot2, mProofUtils.res(ot1, eq1, mProofRules.iffElim2(destEq)), eq2);
			} else {
				// ct1 = false, ct1 = true
				return mProofUtils.res(ot2, eq2, mProofUtils.res(ot1, mProofRules.iffElim1(destEq), eq1));
			}
		}
		if (ot1 != ct1 && ot2 != ct2) {
			return mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ct1, ct2),
					mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ct1, ot1),
							mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ot1, ct1), eq1,
									mProofRules.symm(ct1, ot1)),
							mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ct2, ot2), eq2,
									mProofRules.trans(ct1, ot1, ot2, ct2))),
					mProofUtils.proveDisequality(ct1, ct2));
		} else {
			Term proof = mProofUtils.proveDisequality(ct1, ct2);
			if (ot1 != ct1) {
				proof = mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ct1, ot1),
						mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ot1, ct1), eq1, mProofRules.symm(ct1, ot1)),
						mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ct1, ct2), mProofRules.trans(ct1, ot1, ct2),
								proof));
			}
			if (ot2 != ct2) {
				proof = mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ot2, ct2), eq2, mProofUtils
						.res(theory.term(SMTLIBConstants.EQUALS, ct1, ct2), mProofRules.trans(ct1, ot2, ct2),
								proof));
			}
			return proof;
		}
	}

	private Term proveEquality(Term ot1, Term eq1, Term ct, Term eq2, Term ot2) {
		final Theory theory = ot1.getTheory();
		if (ct.getSort() == theory.getBooleanSort()) {
			final Term destEq = theory.term(SMTLIBConstants.EQUALS, ot1, ot2);
			final boolean isTrue = ct == theory.mTrue;
			if (isTrue) {
				return mProofUtils.res(ot2, eq2, mProofUtils.res(ot1, eq1, mProofRules.iffIntro2(destEq)));
			} else {
				return mProofUtils.res(ot2, mProofUtils.res(ot1, mProofRules.iffIntro1(destEq), eq1), eq2);
			}
		} else {
			if (ot2 == ct) {
				return eq1;
			}
			final Term eq2S = mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ot2, ct), eq2,
					mProofRules.symm(ct, ot2));
			if (ot1 == ct) {
				return eq2S;
			}
			return mProofUtils.res(theory.term(SMTLIBConstants.EQUALS, ot1, ct), eq1, mProofUtils
					.res(theory.term(SMTLIBConstants.EQUALS, ct, ot2), eq2S, mProofRules.trans(ot1, ct, ot2)));
		}
	}

	private Term interpret(Term origTerm, final FunctionSymbol fs, final Term[] args) {
		final Theory theory = fs.getTheory();
		final Term funcTerm = theory.term(fs, args);
		switch (fs.getName()) {
		case SMTLIBConstants.TRUE:
		case SMTLIBConstants.FALSE:
		case SMTLIBConstants.AND:
		case SMTLIBConstants.OR:
		case SMTLIBConstants.IMPLIES:
		case SMTLIBConstants.NOT:
		case SMTLIBConstants.EQUALS:
		case SMTLIBConstants.DISTINCT:
		case SMTLIBConstants.ITE:
			throw new AssertionError("Handled by other function");

		case SMTLIBConstants.XOR: {
			int countTrue = 0;
			int countFalse = 0;
			for (int i = 0; i < args.length; i++) {
				if (args[i] == theory.mTrue) {
					countTrue++;
				} else {
					countFalse++;
				}
			}
			final Term[] false2 = new Term[] { theory.mFalse, theory.mFalse };
			final Term dummy = theory.term(SMTLIBConstants.XOR, false2);
			Term result;
			Term proof;
			if ((countTrue % 2) == 1) {
				// result is true
				if ((countFalse % 2) == 1) {
					proof = mProofRules.xorIntro(args, new Term[] { theory.mFalse }, new Term[] { theory.mTrue });
					proof = mProofUtils.res(theory.mFalse, proof, mProofRules.falseElim());
				} else {
					proof = mProofRules.xorIntro(args, false2, new Term[] { theory.mTrue });
					proof = mProofUtils.res(dummy, proof, mProofRules.xorElim(false2, false2, false2));
				}
				proof = mProofUtils.res(theory.mTrue, mProofRules.trueIntro(), proof);
				result = theory.mTrue;
			} else {
				// result is false
				if ((countFalse % 2) == 0) {
					proof = mProofRules.xorElim(args, args, args);
				} else {
					proof = mProofRules.xorIntro(new Term[] { theory.mFalse }, false2, args);
					proof = mProofUtils.res(dummy, proof, mProofRules.xorElim(false2, false2, false2));
					proof = mProofUtils.res(theory.mFalse, proof, mProofRules.falseElim());
				}
				result = theory.mFalse;
			}
			return annotateProof(proof, result);
		}

		case SMTLIBConstants.PLUS: {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.add(rationalValue(args[i]));
			}
			final Term result = val.toTerm(fs.getReturnSort());
			return annotateProof(mProofRules.polyAdd(funcTerm, result), result);
		}

		case SMTLIBConstants.MINUS: {
			Rational val = rationalValue(args[0]);
			if (args.length == 1) {
				val = val.negate();
				final Term result = val.toTerm(fs.getReturnSort());
				if (result == funcTerm) {
					return annotateProof(mProofRules.refl(funcTerm), funcTerm);
				}
				return annotateProof(mProofUtils.proveUMinusEquality(funcTerm, result), result);
			} else {
				for (int i = 1; i < args.length; ++i) {
					val = val.sub(rationalValue(args[i]));
				}
				final Term result = val.toTerm(fs.getReturnSort());
				return annotateProof(mProofUtils.proveMinusEquality(funcTerm, result), result);
			}
		}

		case SMTLIBConstants.MUL: {
			Rational val = rationalValue(args[0]);
			for (int i = 1; i < args.length; ++i) {
				val = val.mul(rationalValue(args[i]));
			}
			final Term result = val.toTerm(fs.getReturnSort());
			return annotateProof(mProofRules.polyMul(funcTerm, result), result);
		}

		case SMTLIBConstants.DIVIDE: {
			final Rational divisor = rationalValue(args[1]);
			if (divisor.equals(Rational.ZERO)) {
				assert args.length == 2;
				expandFunction((ApplicationTerm) funcTerm, args);
				return null;
			} else {
				final Rational val = rationalValue(args[0]).div(divisor);
				final Term result = val.toTerm(fs.getReturnSort());
				if (result == funcTerm) {
					return annotateProof(mProofRules.refl(funcTerm), funcTerm);
				}
				return annotateProof(mProofUtils.proveDivideEquality(funcTerm, result), result);
			}
		}

		case SMTLIBConstants.LEQ:
		case SMTLIBConstants.LT: {
			// we expand non-binary LEQ/LT/... in convert.
			assert args.length == 2;
			final Rational arg1 = rationalValue(args[0]);
			final Rational arg2 = rationalValue(args[1]);
			final int comparison = arg1.compareTo(arg2);
			if (fs.getName() == SMTLIBConstants.LT ? comparison < 0 : comparison <= 0) {
				final Term inverse;
				final Term totalAx;
				if (fs.getName() == SMTLIBConstants.LT) {
					inverse = theory.term(SMTLIBConstants.LEQ, args[1], args[0]);
					totalAx = mProofRules.total(args[1], args[0]);
				} else {
					inverse = theory.term(SMTLIBConstants.LT, args[1], args[0]);
					totalAx = mProofRules.total(args[0], args[1]);
				}
				return annotateProof(
						mProofUtils.res(inverse, totalAx, mProofRules.farkas(BigInteger.ONE, inverse)),
						theory.mTrue);
			} else {
				return annotateProof(mProofRules.farkas(BigInteger.ONE, funcTerm), theory.mFalse);
			}
		}

		case SMTLIBConstants.DIV: {
			assert args.length == 2;
			final Rational n = rationalValue(args[1]);
			if (n.equals(Rational.ZERO)) {
				expandFunction((ApplicationTerm) funcTerm, args);
				return null;
			} else {
				Rational val = rationalValue(args[0]).div(n);
				val = n.isNegative() ? val.ceil() : val.floor();
				final Term result = val.toTerm(fs.getReturnSort());
				return annotateProof(mProofUtils.proveDivEquality(funcTerm, result), result);
			}
		}

		case SMTLIBConstants.MOD: {
			assert args.length == 2;
			final Rational n = rationalValue(args[1]);
			if (n.equals(Rational.ZERO)) {
				expandFunction((ApplicationTerm) funcTerm, args);
				return null;
			} else {
				final Rational m = rationalValue(args[0]);
				Rational div = m.div(n);
				div = n.isNegative() ? div.ceil() : div.floor();
				final Term result = m.sub(div.mul(n)).toTerm(fs.getReturnSort());
				return annotateProof(mProofUtils.proveModConstant(funcTerm, result), result);
			}
		}

		case SMTLIBConstants.ABS: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			final Term result = arg.abs().toTerm(fs.getReturnSort());
			return annotateProof(mProofUtils.proveAbsConstant(arg, fs.getReturnSort()), result);
		}

		case SMTLIBConstants.DIVISIBLE: {
			assert args.length == 1;
			final Term arg = args[0];
			final String[] indices = fs.getIndices();
			assert indices.length == 1;
			BigInteger divisor;
			try {
				divisor = new BigInteger(indices[0]);
			} catch (final NumberFormatException e) {
				throw new SMTLIBException("index of divisible must be numeral", e);
			}
			// divisible-def: (= ((_ divisible d) x) (= x (* d (div x d))))
			final Rational rdivisor = Rational.valueOf(divisor, BigInteger.ONE);
			final Term divisorTerm = rdivisor.toTerm(arg.getSort());
			final Term divisibleDef = theory.term(SMTLIBConstants.EQUALS, arg,
					theory.term(SMTLIBConstants.MUL, divisorTerm, theory.term(SMTLIBConstants.DIV, arg, divisorTerm)));
			enqueueTransitivityStep(funcTerm, divisibleDef, mProofRules.expand(funcTerm));
			pushTerm(divisibleDef);
			return null;
		}

		case SMTLIBConstants.TO_INT: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			final Term result = arg.floor().toTerm(fs.getReturnSort());
			return annotateProof(mProofUtils.proveToIntConstant(funcTerm, result), result);
		}

		case SMTLIBConstants.TO_REAL: {
			assert args.length == 1;
			final Rational arg = rationalValue(args[0]);
			return annotateProof(mProofRules.toRealDef(args[0]), arg.toTerm(fs.getReturnSort()));
		}

		case SMTLIBConstants.STORE: {
			final ArraySortInterpretation array = (ArraySortInterpretation) mModel
					.provideSortInterpretation(fs.getParameterSorts()[0]);
			return array.normalizeStoreTerm(theory.term(fs, args));
		}

		case SMTLIBConstants.CONST:
			return theory.term(fs, args[0]);

		case SMTLIBConstants.SELECT: {
			// we assume that the array parameter is a term of the form
			// store(store(...(const v) ...))
			ApplicationTerm array = (ApplicationTerm) args[0];
			final Term index = args[1];
			FunctionSymbol head = array.getFunction();
			// go through the store chain and check if we write to the index
			while (head.getName() == SMTLIBConstants.STORE) {
				if (array.getParameters()[1] == index) {
					final Term result = array.getParameters()[2];
					return annotateProof(mProofUtils.proveSelectOverStore(funcTerm, result), result);
				}
				array = (ApplicationTerm) array.getParameters()[0];
				head = array.getFunction();
			}
			assert head.getName() == SMTLIBConstants.CONST;
			final Term result = array.getParameters()[0];
			return annotateProof(mProofUtils.proveSelectOverStore(funcTerm, result), result);
		}

		case SMTInterpolConstants.DIFF: {
			final ArraySortInterpretation array = (ArraySortInterpretation) mModel
					.provideSortInterpretation(fs.getParameterSorts()[0]);
			return array.computeDiff(args[0], args[1], fs.getReturnSort());
		}

		case SMTLIBConstants.INT_TO_BV: {
			assert args.length == 1;
			final Rational n = rationalValue(args[0]);
			assert n.isIntegral();
			final BigInteger mask = getBVModulo(fs.getReturnSort()).subtract(BigInteger.ONE);
			final Term result = createBitvectorTerm(n.numerator().and(mask), fs.getReturnSort());
			return annotateProof(mProofUtils.proveIntToBvConstant(args[0], new BigInteger(fs.getIndices()[0])), result);
		}

		case SMTLIBConstants.UBV_TO_INT: {
			assert args.length == 1;
			final BigInteger value = bitvectorValue(args[0]);
			final Term result = Rational.valueOf(value, BigInteger.ONE).toTerm(fs.getReturnSort());
			return annotateProof(mProofUtils.proveUbvToIntConstant(args[0]), result);
		}

		case SMTLIBConstants.SBV_TO_INT: {
			assert args.length == 1;
			BigInteger value = bitvectorValue(args[0]);
			final int bitlength = getBitVecSize(args[0].getSort());
			final BigInteger signBit = BigInteger.ONE.shiftLeft(bitlength - 1);
			if (value.compareTo(signBit) >= 0) {
				value = value.subtract(BigInteger.ONE.shiftLeft(bitlength));
			}
			final Term result = Rational.valueOf(value, BigInteger.ONE).toTerm(fs.getReturnSort());
			return annotateProof(mProofUtils.proveSbvToIntConstant(args[0]), result);
		}

		case SMTInterpolConstants.INTAND: {
			BigInteger value = rationalValue(args[0]).numerator();
			for (int i = 1; i < args.length; i++) {
				final BigInteger arg = rationalValue(args[i]).numerator();
				value = value.and(arg);
			}
			final Term result = Rational.valueOf(value, BigInteger.ONE).toTerm(origTerm.getSort());
			final Term defEq = theory.term(SMTLIBConstants.EQUALS, funcTerm, result);
			final ProofLiteral[] proofLits = new ProofLiteral[] {
					new ProofLiteral(defEq, true)
			};
			return annotateProof(
					mProofRules.oracle(proofLits, new Annotation[] { new Annotation(":intand-const", args) }), result);
		}

		case SMTLIBConstants.BVNAND: {
			assert args.length == 2;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger value = modulo.subtract(BigInteger.ONE)
					.subtract(bitvectorValue(args[0]).and(bitvectorValue(args[1])));
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVNOR: {
			assert args.length == 2;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger value = modulo.subtract(BigInteger.ONE)
					.subtract(bitvectorValue(args[0]).or(bitvectorValue(args[1])));
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVXNOR: {
			assert args.length == 2;
			final BigInteger modulo = getBVModulo(fs.getReturnSort());
			final BigInteger value = modulo.subtract(BigInteger.ONE)
					.subtract(bitvectorValue(args[0]).xor(bitvectorValue(args[1])));
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVCOMP: {
			assert args.length == 2;
			final BigInteger value = bitvectorValue(args[0]).equals(bitvectorValue(args[1])) ? BigInteger.ONE
					: BigInteger.ZERO;
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case SMTLIBConstants.BVULE: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) <= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVULT: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) < 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVUGE: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) >= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVUGT: {
			assert args.length >= 2;
			boolean result = true;
			BigInteger lastArg = bitvectorValue(args[0]);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]);
				result &= lastArg.compareTo(nextArg) > 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSLE: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) <= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSLT: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) < 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSGE: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) >= 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSGT: {
			assert args.length >= 2;
			boolean result = true;
			final BigInteger signBit = BigInteger.ONE.shiftLeft(getBitVecSize(args[0].getSort()) - 1);
			BigInteger lastArg = bitvectorValue(args[0]).xor(signBit);
			for (int i = 1; i < args.length; i++) {
				final BigInteger nextArg = bitvectorValue(args[i]).xor(signBit);
				result &= lastArg.compareTo(nextArg) > 0;
				lastArg = nextArg;
			}
			return result ? theory.mTrue : theory.mFalse;
		}
		case SMTLIBConstants.BVSHL: {
			final int size = getBitVecSize(fs.getReturnSort());
			assert args.length == 2;
			final BigInteger shiftArg = bitvectorValue(args[1]);
			BigInteger value;
			if (shiftArg.compareTo(BigInteger.valueOf(size)) < 0) {
				assert shiftArg.bitLength() <= 32;
				final BigInteger mask = BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE);
				value = bitvectorValue(args[0]).shiftLeft(shiftArg.intValue()).and(mask);
			} else {
				value = BigInteger.ZERO;
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.BVLSHR: {
			final int size = getBitVecSize(fs.getReturnSort());
			assert args.length == 2;
			final BigInteger shiftArg = bitvectorValue(args[1]);
			BigInteger value;
			if (shiftArg.compareTo(BigInteger.valueOf(size)) < 0) {
				assert shiftArg.bitLength() <= 32;
				value = bitvectorValue(args[0]).shiftRight(shiftArg.intValue());
			} else {
				value = BigInteger.ZERO;
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.BVASHR: {
			final int size = getBitVecSize(fs.getReturnSort());
			assert args.length == 2;
			final BigInteger shiftArg = bitvectorValue(args[1]);
			BigInteger value = bitvectorValue(args[0]);
			if (shiftArg.compareTo(BigInteger.valueOf(size)) < 0) {
				assert shiftArg.bitLength() <= 32;
				final int shiftInt = shiftArg.intValue();
				final BigInteger signBits = value.testBit(size - 1)
						? BigInteger.ONE.shiftLeft(size - shiftInt).subtract(BigInteger.ONE).shiftLeft(shiftInt)
						: BigInteger.ZERO;
				value = value.shiftRight(shiftInt).or(signBits);
			} else {
				value = value.testBit(size - 1) ? BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE)
						: BigInteger.ZERO;
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.CONCAT: {
			assert args.length == 2;
			final int size2 = getBitVecSize(args[1].getSort());
			final BigInteger value = bitvectorValue(args[0]).shiftLeft(size2).or(bitvectorValue(args[1]));
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.REPEAT: {
			assert args.length == 1;
			final int sizeIn = getBitVecSize(args[0].getSort());
			final int count = Integer.parseInt(fs.getIndices()[0]);
			final BigInteger multiplier = BigInteger.ONE.shiftLeft(sizeIn * count).subtract(BigInteger.ONE)
					.divide(BigInteger.ONE.shiftLeft(sizeIn).subtract(BigInteger.ONE));
			final BigInteger value = bitvectorValue(args[0]).multiply(multiplier);
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.EXTRACT: {
			assert args.length == 1;
			final int high = Integer.parseInt(fs.getIndices()[0]);
			final int low = Integer.parseInt(fs.getIndices()[1]);
			final BigInteger value = bitvectorValue(args[0]).shiftRight(low)
					.and(BigInteger.ONE.shiftLeft(high - low + 1).subtract(BigInteger.ONE));
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.ZERO_EXTEND: {
			return createBitvectorTerm(bitvectorValue(args[0]), fs.getReturnSort());
		}
		case SMTLIBConstants.SIGN_EXTEND: {
			assert args.length == 1;
			final int inputLen = getBitVecSize(args[0].getSort());
			BigInteger value = bitvectorValue(args[0]);
			if (value.testBit(inputLen - 1)) {
				final int outputLen = getBitVecSize(fs.getReturnSort());
				value = value.add(BigInteger.ONE.shiftLeft(outputLen).subtract(BigInteger.ONE.shiftLeft(inputLen)));
			}
			return createBitvectorTerm(value, fs.getReturnSort());
		}
		case SMTLIBConstants.ROTATE_LEFT:
		case SMTLIBConstants.ROTATE_RIGHT: {
			assert args.length == 1;
			final int size = getBitVecSize(fs.getReturnSort());
			int rotateValue = Integer.parseInt(fs.getIndices()[0]);
			if (fs.getName().equals(SMTLIBConstants.ROTATE_RIGHT)) {
				rotateValue = size - rotateValue;
			}
			final BigInteger mask = BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE);
			BigInteger value = bitvectorValue(args[0]);
			value = value.shiftLeft(rotateValue).or(value.shiftRight(size - rotateValue)).and(mask);
			return createBitvectorTerm(value, fs.getReturnSort());
		}

		case "@EQ": {
			expandFunction((ApplicationTerm) funcTerm, args);
			return null;
		}
		default:
			if (fs.isConstructor()) {
				return annotateProof(mProofRules.refl(funcTerm), funcTerm);
			} else if (fs.isSelector()) {
				final ApplicationTerm arg = (ApplicationTerm) args[0];
				final DataType dataType = (DataType) arg.getSort().getSortSymbol();
				assert arg.getFunction().isConstructor();
				final Constructor constr = dataType.getConstructor(arg.getFunction().getName());
				final String[] selectors = constr.getSelectors();
				for (int i = 0; i < selectors.length; i++) {
					if (selectors[i].equals(fs.getName())) {
						return annotateProof(mProofRules.dtProject(funcTerm), arg.getParameters()[i]);
					}
				}
				// undefined case for selector on wrong constructor. use model.
				expandFunction((ApplicationTerm) funcTerm, args);
				return null;
			} else if (fs.getName().equals(SMTLIBConstants.IS)) {
				final ApplicationTerm arg = (ApplicationTerm) args[0];
				assert arg.getFunction().isConstructor();
				final boolean isTrue = arg.getFunction().getName().equals(fs.getIndices()[0]);
				return annotateProof(isTrue ? mProofRules.dtTestI(arg) : mProofRules.dtTestE(fs.getIndices()[0], arg),
						isTrue ? theory.mTrue : theory.mFalse);
			}
			throw new AssertionError("Unknown internal function " + fs.getName());
		}
	}

	private Rational rationalValue(final Term term) {
		return (Rational) ((ConstantTerm) term).getValue();
	}

	private BigInteger bitvectorValue(Term t) {
		return (BigInteger) ((ConstantTerm) t).getValue();
	}

	private Term createBitvectorTerm(BigInteger value, Sort sort) {
		return BitVectorInterpretation.BV(value, sort);
	}

	private int getBitVecSize(Sort sort) {
		assert sort.isBitVecSort();
		return Integer.parseInt(sort.getIndices()[0]);
	}

	private BigInteger getBVModulo(Sort sort) {
		return BigInteger.ONE.shiftLeft(getBitVecSize(sort));
	}

	private Term createAnd(Term[] args) {
		final Theory theory = mModel.getTheory();
		return args.length == 0 ? theory.mTrue : args.length == 1 ? args[0] : theory.term(SMTLIBConstants.AND, args);
	}

	public Term buildModelProof(List<Term> assertions) {
		final Term[] andArgs = assertions.toArray(new Term[assertions.size()]);
		final Term andTerm = createAnd(andArgs);
		final Term provedTerm = transform(mUnletter.transform(andTerm));
		assert getAnnotation(provedTerm) == provedTerm.getTheory().mTrue;
		Term proof = getProof(provedTerm);
		for (final FunctionSymbol fs : mModel.getDefinedFunctions()) {
			final Term definition = mModel.getFunctionDefinition(fs);
			proof = mProofRules.refineFun(fs, definition, proof);
		}
		return proof;
	}
}
