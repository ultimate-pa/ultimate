/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Transform Boolean Term into negation normal form.
 *
 * @author heizmann@informatik.uni-freiburg.de
 */
public class NnfTransformer {

	protected final Script mScript;
	private static final String s_FreshVariableString = "nnf";
	private final ManagedScript mMgdScript;
	protected final ILogger mLogger;
	private final NnfTransformerHelper mNnfTransformerHelper;
	private List<List<TermVariable>> mQuantifiedVariables;

	public enum QuantifierHandling {
		/**
		 * Throw an UnsupportedOperationException if quantified formula is encountered.
		 */
		CRASH,
		/**
		 * Keep quantifier at the position where it occurred, but replace by dual quantifier if necessary. E.g., ¬∀φ
		 * becomes Ǝ¬φ.
		 */
		KEEP,
		/**
		 * Consider quantified formulas as atoms do not descend into the body of the quantified formula.
		 */
		IS_ATOM,
		/**
		 * Pull quantifiers to the front. I.e., the resulting formula will be in prenex normal form. 2018-06-01
		 * Matthias: better use {@link PrenexNormalForm} instead, PULL may produce formulas with more quantifier
		 * alternations.
		 */
		PULL
	}

	protected final QuantifierHandling mQuantifierHandling;

	protected Function<Integer, Boolean> mFunAbortIfExponential;

	/**
	 * Sometimes we need to omit the soundness check which does a checksat on mManagedScript. For example, this is the
	 * case when mManagedScript.getScript is HornClauseParserScript (in which case the soundness check would lead to
	 * nontermination)
	 */
	private final boolean mOmitSoundnessCheck;

	public NnfTransformer(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final QuantifierHandling quantifierHandling) {
		this(mgdScript, services, quantifierHandling, false, a -> false);
	}

	public NnfTransformer(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final QuantifierHandling quantifierHandling, final boolean omitSoundnessCheck) {
		this(mgdScript, services, quantifierHandling, omitSoundnessCheck, a -> false);
	}

	public NnfTransformer(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final QuantifierHandling quantifierHandling, final boolean omitSoundnessCheck,
			final Function<Integer, Boolean> funAbortIfExponential) {
		mFunAbortIfExponential = Objects.requireNonNull(funAbortIfExponential);
		mQuantifierHandling = quantifierHandling;
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mNnfTransformerHelper = getNnfTransformerHelper(services);
		mOmitSoundnessCheck = omitSoundnessCheck;
	}

	protected NnfTransformerHelper getNnfTransformerHelper(final IUltimateServiceProvider services) {
		return new NnfTransformerHelper(services);
	}

	public Term transform(final Term term) {
		assert mQuantifiedVariables == null;
		if (mQuantifierHandling == QuantifierHandling.PULL) {
			mQuantifiedVariables = new ArrayList<>();
			final List<TermVariable> firstQuantifierBlock = new ArrayList<>();
			mQuantifiedVariables.add(firstQuantifierBlock);
		}
		Term result = mNnfTransformerHelper.transform(term);
		if (mQuantifierHandling == QuantifierHandling.PULL) {
			for (int i = 0; i < mQuantifiedVariables.size(); i++) {
				final TermVariable[] variables =
						mQuantifiedVariables.get(i).toArray(new TermVariable[mQuantifiedVariables.get(i).size()]);
				if (variables.length > 0) {
					final int quantor = i % 2;
					result = mScript.quantifier(quantor, variables, result);
				}
			}
			mQuantifiedVariables = null;
		}
		assert mOmitSoundnessCheck || Util.checkSat(mScript,
				mScript.term("distinct", term, result)) != LBool.SAT : "Nnf transformation unsound";
		return result;
	}

	protected class NnfTransformerHelper extends TermTransformer {

		protected IUltimateServiceProvider mServices;

		protected NnfTransformerHelper(final IUltimateServiceProvider services) {
			mServices = services;
		}

		@Override
		protected void convert(final Term term) {
			assert SmtSortUtils.isBoolSort(term.getSort()) : "Input is not Bool";
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				final String functionName = appTerm.getFunction().getName();
				if (functionName.equals("and")) {
					final Term flattened = SmtUtils.and(mScript, appTerm.getParameters());
					if (SmtUtils.isFunctionApplication(flattened, "and")) {
						super.convert(flattened);
					} else {
						// term was simplified by flattening, top function
						// symbol changed, call convert again
						convert(flattened);
					}
					return;
				} else if (functionName.equals("or")) {
					final Term flattened = SmtUtils.or(mScript, appTerm.getParameters());
					if (SmtUtils.isFunctionApplication(flattened, "or")) {
						super.convert(flattened);
					} else {
						// term was simplified by flattening, top function
						// symbol changed, call convert again
						convert(flattened);
					}
					return;
				} else if (functionName.equals("not")) {
					assert appTerm.getParameters().length == 1;
					final Term notParam = appTerm.getParameters()[0];
					convertNot(notParam, term);
					return;
				} else if (functionName.equals("=>")) {
					final Term[] params = appTerm.getParameters();
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(SmtUtils.or(mScript, negateAllButLast(mScript, params)));
					return;
				} else if (functionName.equals("=") && SmtUtils.firstParamIsBool(appTerm)) {
					final Term[] params = appTerm.getParameters();
					if (params.length > 2) {
						final Term binarized = SmtUtils.binarize(mScript, appTerm);
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(binarized);
					} else {
						assert params.length == 2;
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(SmtUtils.binaryBooleanEquality(mScript, params[0], params[1]));
					}
				} else if (isXor(appTerm, functionName)) {
					final Term[] params = appTerm.getParameters();
					if (params.length > 2) {
						final Term binarized = SmtUtils.binarize(mScript, appTerm);
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(binarized);
					} else {
						assert params.length == 2;
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(SmtUtils.binaryBooleanNotEquals(mScript, params[0], params[1]));
					}
				} else if (functionName.equals("ite") && SmtUtils.allParamsAreBool(appTerm)) {
					final Term[] params = appTerm.getParameters();
					assert params.length == 3;
					final Term condTerm = params[0];
					final Term ifTerm = params[1];
					final Term elseTerm = params[2];
					final Term result = convertIte(mScript, condTerm, ifTerm, elseTerm);
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(result);
					return;
				} else {
					// consider term as atom
					setResult(term);
					return;
				}
			} else if (term instanceof TermVariable) {
				// consider term as atom
				setResult(term);
			} else if (term instanceof ConstantTerm) {
				// consider term as atom
				setResult(term);
			} else if (term instanceof QuantifiedFormula) {
				switch (mQuantifierHandling) {
				case CRASH: {
					throw new UnsupportedOperationException("quantifier handling set to " + mQuantifierHandling);
				}
				case IS_ATOM: {
					// consider quantified formula as atom
					setResult(term);
					return;
				}
				case KEEP: {
					super.convert(term);
					return;
				}
				case PULL: {
					final QuantifiedFormula qf = (QuantifiedFormula) term;
					final List<TermVariable> variables;
					if (mQuantifiedVariables.size() - 1 == qf.getQuantifier()) {
						variables = mQuantifiedVariables.get(mQuantifiedVariables.size() - 1);
					} else {
						variables = new ArrayList<>();
						mQuantifiedVariables.add(variables);
					}
					final Map<Term, Term> substitutionMapping = new HashMap<>();
					for (final TermVariable oldTv : qf.getVariables()) {
						final TermVariable freshTv =
								mMgdScript.constructFreshTermVariable(s_FreshVariableString, oldTv.getSort());
						substitutionMapping.put(oldTv, freshTv);
						variables.add(freshTv);
					}
					final Term newBody = new Substitution(mScript, substitutionMapping).transform(qf.getSubformula());
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(newBody);
					return;
				}
				default:
					throw new AssertionError("unknown case");
				}
			} else if (term instanceof AnnotatedTerm) {
				mLogger.warn("thrown away annotations " + Arrays.toString(((AnnotatedTerm) term).getAnnotations()));
				convert(((AnnotatedTerm) term).getSubterm());
			}
		}

		private void convertNot(final Term notParam, final Term notTerm) {
			assert SmtSortUtils.isBoolSort(notParam.getSort()) : "Input is not Bool";
			final Term pushed = pushNot1StepInside(mScript, notParam, mQuantifierHandling);
			if (pushed == null) {
				setResult(notTerm);
			} else {
				// we deliberately call convert() instead of super.convert()
				// the argument of this call might have been simplified
				// to a term whose function symbol is neither "and" nor "or"
				convert(pushed);
			}
			return;
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final Term simplified = SmtUtils.termWithLocalSimplification(mScript, appTerm.getFunction(), newArgs);
			setResult(simplified);
		}

	}

	private static Term[] negateTerms(final Script script, final Term[] terms) {
		final Term[] newTerms = new Term[terms.length];
		for (int i = 0; i < terms.length; i++) {
			newTerms[i] = SmtUtils.not(script, terms[i]);
		}
		return newTerms;
	}

	private static Term[] negateLast(final Script script, final Term[] terms) {
		final Term[] newTerms = new Term[terms.length];
		System.arraycopy(terms, 0, newTerms, 0, terms.length - 1);
		newTerms[terms.length - 1] = SmtUtils.not(script, terms[terms.length - 1]);
		return newTerms;
	}

	private static Term[] negateAllButLast(final Script script, final Term[] terms) {
		final Term[] newTerms = new Term[terms.length];
		for (int i = 0; i < terms.length - 1; i++) {
			newTerms[i] = SmtUtils.not(script, terms[i]);
		}
		newTerms[terms.length - 1] = terms[terms.length - 1];
		return newTerms;
	}

	public static Term convertIte(final Script script, final Term condTerm, final Term ifTerm, final Term elseTerm) {
		final Term condImpliesIf = SmtUtils.or(script, SmtUtils.not(script, condTerm), ifTerm);
		final Term notCondImpliesElse = SmtUtils.or(script, condTerm, elseTerm);
		final Term result = SmtUtils.and(script, condImpliesIf, notCondImpliesElse);
		return result;
	}

	/**
	 * A function is an xor if one of the following applies.
	 * <ul>
	 * <li>its functionName is <b>xor</b>
	 * <li>its functionName is <b>distinct</b> and its parameters have Sort Bool.
	 * </ul>
	 */
	public static boolean isXor(final ApplicationTerm appTerm, final String functionName) {
		return functionName.equals("xor") || functionName.equals("distinct") && SmtUtils.firstParamIsBool(appTerm);
	}

	public static Term pushNot1StepInside(final Script script, final Term notParam,
			final QuantifierHandling quantifierHandling) {
		if (notParam instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) notParam;
			final String functionName = appTerm.getFunction().getName();
			final Term[] params = appTerm.getParameters();
			if (functionName.equals("and")) {
				return SmtUtils.or(script, negateTerms(script, params));
			} else if (functionName.equals("or")) {
				return SmtUtils.and(script, negateTerms(script, params));
			} else if (functionName.equals("not")) {
				assert appTerm.getParameters().length == 1;
				final Term notnotParam = appTerm.getParameters()[0];
				return notnotParam;
			} else if (functionName.equals("=>")) {
				return SmtUtils.and(script, negateLast(script, params));
			} else if (functionName.equals("=") && SmtUtils.firstParamIsBool(appTerm)) {
				final Term[] notParams = appTerm.getParameters();
				if (notParams.length > 2) {
					final Term binarized = SmtUtils.binarize(script, appTerm);
					return SmtUtils.not(script, binarized);
				} else {
					assert notParams.length == 2;
					return SmtUtils.binaryBooleanNotEquals(script, notParams[0], notParams[1]);
				}
			} else if (isXor(appTerm, functionName)) {
				final Term[] notParams = appTerm.getParameters();
				if (notParams.length > 2) {
					final Term binarized = SmtUtils.binarize(script, appTerm);
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					return SmtUtils.not(script, binarized);
				} else {
					assert notParams.length == 2;
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					return SmtUtils.binaryBooleanEquality(script, notParams[0], notParams[1]);
				}
			} else if (functionName.equals("ite") && SmtUtils.allParamsAreBool(appTerm)) {
				final Term[] notParams = appTerm.getParameters();
				assert params.length == 3;
				final Term condTerm = notParams[0];
				final Term ifTerm = notParams[1];
				final Term elseTerm = notParams[2];
				final Term convertedIte = convertIte(script, condTerm, ifTerm, elseTerm);
				return SmtUtils.not(script, convertedIte);
			} else {
				// consider original term as atom
				// nothing to push inside, return null;
				return null;
			}
		} else if (notParam instanceof QuantifiedFormula) {
			switch (quantifierHandling) {
			case CRASH: {
				throw new UnsupportedOperationException("quantifier handling set to " + quantifierHandling);
			}
			case IS_ATOM: {
				return null;
			}
			case KEEP: {
				final QuantifiedFormula qformula = (QuantifiedFormula) notParam;
				final Term inner = qformula.getSubformula();
				final Term innerNegated = SmtUtils.not(script, inner);
				final int dualQuantifier = QuantifierUtils.getDualQuantifier(qformula.getQuantifier());
				final Term result = SmtUtils.quantifier(script, dualQuantifier,
						new HashSet<>(Arrays.asList(qformula.getVariables())), innerNegated);
				return result;
			}
			case PULL: {
				throw new UnsupportedOperationException(
						"20180601 Matthias: I am not sure if we should still support PULL");
			}
			default: {
				throw new AssertionError();
			}
			}
		} else {
			return null;
		}
	}

}
