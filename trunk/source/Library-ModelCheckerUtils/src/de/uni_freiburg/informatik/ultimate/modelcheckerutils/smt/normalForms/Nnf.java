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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;


/**
 * Transform Boolean Term into negation normal form.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class Nnf {
	
	protected final Script m_Script;
	private static final String s_FreshVariableString = "nnf";
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;
	protected final Logger m_Logger;
	private final NnfTransformerHelper m_NnfTransformerHelper;
	private List<List<TermVariable>> m_QuantifiedVariables;
	
	public enum QuantifierHandling { CRASH, PULL, KEEP, IS_ATOM }
	protected final QuantifierHandling m_QuantifierHandling;
	
	public Nnf(Script script, IUltimateServiceProvider services, 
			IFreshTermVariableConstructor freshTermVariableConstructor,
			QuantifierHandling quantifierHandling) {
		super();
		m_QuantifierHandling = quantifierHandling;
		m_Script = script;
		m_FreshTermVariableConstructor = freshTermVariableConstructor;
		m_Logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		m_NnfTransformerHelper = getNnfTransformerHelper(services);
	}
	
	protected NnfTransformerHelper getNnfTransformerHelper(IUltimateServiceProvider services) {
		return new NnfTransformerHelper(services);
	}
	
	public Term transform(Term term) {
		assert m_QuantifiedVariables == null;
		if (m_QuantifierHandling == QuantifierHandling.PULL) {
			m_QuantifiedVariables = new ArrayList<List<TermVariable>>();
			List<TermVariable> firstQuantifierBlock = new ArrayList<TermVariable>();
			m_QuantifiedVariables.add(firstQuantifierBlock);
		}
		Term result = m_NnfTransformerHelper.transform(term);
		if (m_QuantifierHandling == QuantifierHandling.PULL) {
			for (int i=0; i<m_QuantifiedVariables.size(); i++) {
				TermVariable[] variables = m_QuantifiedVariables.get(i).toArray(new TermVariable[m_QuantifiedVariables.get(i).size()]);
				if (variables.length > 0) {
					int quantor = i%2;
					assert QuantifiedFormula.EXISTS == 0;
					assert QuantifiedFormula.FORALL == 1;
					result = m_Script.quantifier(quantor, variables, result);
				}
			}
			m_QuantifiedVariables = null;
		}
		assert (Util.checkSat(m_Script, m_Script.term("distinct", term, result)) != LBool.SAT) : "Nnf transformation unsound";
		return result;
	}

	protected class NnfTransformerHelper extends TermTransformer {
		
		protected IUltimateServiceProvider mServices;

		protected NnfTransformerHelper(IUltimateServiceProvider services){
			mServices = services;
		}
		
		@Override
		protected void convert(Term term) {
			assert term.getSort().getName().equals("Bool") : "Input is not Bool";
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term; 
				String functionName = appTerm.getFunction().getName();
				if (functionName.equals("and")) {
					final Term flattened = Util.and(m_Script, appTerm.getParameters());
					if (SmtUtils.isFunctionApplication(flattened, "and")) {
						super.convert(flattened);
					} else {
						// term was simplified by flattening, top function 
						// symbol changed, call convert again
						convert(flattened);
					}
					return;
				} else if (functionName.equals("or")) {
					final Term flattened = Util.or(m_Script, appTerm.getParameters());
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
					Term notParam = appTerm.getParameters()[0];
					convertNot(notParam, term);
					return;
				} else if (functionName.equals("=>")) {
					Term[] params = appTerm.getParameters();
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(Util.or(m_Script, negateAllButLast(params)));
					return;
				} else if (functionName.equals("=") && 
						SmtUtils.firstParamIsBool(appTerm)) {
					Term[] params = appTerm.getParameters();
					if (params.length > 2) {
						Term binarized = SmtUtils.binarize(m_Script, appTerm);
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(binarized);
					} else {
						assert params.length == 2;
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(SmtUtils.binaryBooleanEquality(
								m_Script, params[0], params[1]));
					}
				} else if (isXor(appTerm, functionName)) {
					Term[] params = appTerm.getParameters();
					if (params.length > 2) {
						Term binarized = SmtUtils.binarize(m_Script, appTerm);
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(binarized);
					} else {
						assert params.length == 2;
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(SmtUtils.binaryBooleanNotEquals(
								m_Script, params[0], params[1]));
					}
				} else if (functionName.equals("ite") && SmtUtils.allParamsAreBool(appTerm)) {
					Term[] params = appTerm.getParameters();
					assert params.length == 3;
					Term condTerm = params[0];
					Term ifTerm = params[1];
					Term elseTerm = params[2];
					Term result = convertIte(condTerm, ifTerm, elseTerm);
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(result);
					return;
				} else {
					//consider term as atom
					setResult(term);
					return;
				}
			} else if (term instanceof TermVariable) {
				//consider term as atom
				setResult(term);
			} else if (term instanceof ConstantTerm) {
				//consider term as atom
				setResult(term);
			}else if (term instanceof QuantifiedFormula) {
				switch (m_QuantifierHandling) {
				case CRASH: {
					throw new UnsupportedOperationException(
							"quantifier handling set to " + m_QuantifierHandling);
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
					if (m_QuantifiedVariables.size()-1 == qf.getQuantifier()) {
						assert QuantifiedFormula.EXISTS == 0;
						assert QuantifiedFormula.FORALL == 1;
						variables = m_QuantifiedVariables.get(m_QuantifiedVariables.size()-1);
					} else {
						variables = new ArrayList<TermVariable>();
						m_QuantifiedVariables.add(variables);
					}
					final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
					for (TermVariable oldTv : qf.getVariables()) {
						final TermVariable freshTv = m_FreshTermVariableConstructor.
								constructFreshTermVariable(s_FreshVariableString, oldTv.getSort()); 
						substitutionMapping.put(oldTv, freshTv);
						variables.add(freshTv);
					}
					Term newBody = (new SafeSubstitution(m_Script, substitutionMapping)).transform(qf.getSubformula());
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
				m_Logger.warn("thrown away annotations " + 
						Arrays.toString(((AnnotatedTerm) term).getAnnotations()));
				convert(((AnnotatedTerm) term).getSubterm());
			}
		}

		private Term convertIte(Term condTerm, Term ifTerm, Term elseTerm) {
			Term condImpliesIf = Util.or(m_Script, Util.not(m_Script, condTerm), ifTerm);
			Term notCondImpliesElse = Util.or(m_Script, condTerm, elseTerm);
			Term result = Util.and(m_Script, condImpliesIf, notCondImpliesElse);
			return result;
		}

		/**
		 * A function is an xor if one of the following applies.
		 * <ul>
		 * <li> its functionName is <b>xor</b> 
		 * <li> its functionName is <b>distinct</b> and its parameters have
		 * Sort Bool.
		 * </ul>
		 */
		private boolean isXor(ApplicationTerm appTerm, String functionName) {
			return functionName.equals("xor") || 
					(functionName.equals("distinct") && SmtUtils.firstParamIsBool(appTerm));
		}
		
		
		private void convertNot(Term notParam, Term notTerm) {
			assert notParam.getSort().getName().equals("Bool") : "Input is not Bool";
			if (notParam instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) notParam; 
				String functionName = appTerm.getFunction().getName();
				Term[] params = appTerm.getParameters();
				if (functionName.equals("and")) {
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(Util.or(m_Script, negateTerms(params)));
					return;
				} else if (functionName.equals("or")) {
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(Util.and(m_Script, negateTerms(params)));
					return;
				} else if (functionName.equals("not")) {
					assert appTerm.getParameters().length == 1;
					Term notnotParam = appTerm.getParameters()[0];
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(notnotParam);
					return;
				} else if (functionName.equals("=>")) {
					// we deliberately call convert() instead of super.convert()
					// the argument of this call might have been simplified
					// to a term whose function symbol is neither "and" nor "or"
					convert(Util.and(m_Script, negateLast(params)));
					return;
				} else if (functionName.equals("=") && 
						SmtUtils.firstParamIsBool(appTerm)) {
					Term[] notParams = appTerm.getParameters();
					if (notParams.length > 2) {
						Term binarized = SmtUtils.binarize(m_Script, appTerm);
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(Util.not(m_Script, binarized));
					} else {
						assert notParams.length == 2;
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(SmtUtils.binaryBooleanNotEquals(
								m_Script, notParams[0], notParams[1]));
					}
				} else if (isXor(appTerm, functionName)) {
					Term[] notParams = appTerm.getParameters();
					if (notParams.length > 2) {
						Term binarized = SmtUtils.binarize(m_Script, appTerm);
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(Util.not(m_Script, binarized));
					} else {
						assert notParams.length == 2;
						// we deliberately call convert() instead of super.convert()
						// the argument of this call might have been simplified
						// to a term whose function symbol is neither "and" nor "or"
						convert(SmtUtils.binaryBooleanEquality(
								m_Script, notParams[0], notParams[1]));
					}
				} else if (functionName.equals("ite") && SmtUtils.allParamsAreBool(appTerm)) {
					Term[] notParams = appTerm.getParameters();
					assert params.length == 3;
					Term condTerm = notParams[0];
					Term ifTerm = notParams[1];
					Term elseTerm = notParams[2];
					Term convertedIte = convertIte(condTerm, ifTerm, elseTerm);
					convertNot(convertedIte, Util.not(m_Script, convertedIte));
				} else {
					//consider original term as atom
					setResult(notTerm);
					return;
				}
			} else if (notParam instanceof ConstantTerm) {
				//consider term as atom
				setResult(notTerm);
			} else if (notParam instanceof TermVariable) {
				//consider term as atom
				setResult(notTerm);
			} else if (notParam instanceof QuantifiedFormula) {
				switch (m_QuantifierHandling) {
				case CRASH: {
					throw new UnsupportedOperationException(
							"quantifier handling set to " + m_QuantifierHandling);
				}
				case IS_ATOM: {
					// consider quantified formula as atom
					setResult(notParam);
					return;
				}
				case KEEP: {
					final QuantifiedFormula qf = (QuantifiedFormula) notParam;
					final int quantor = (qf.getQuantifier() + 1) % 2;
					final TermVariable[] vars = qf.getVariables();
					final Term body = Util.not(m_Script, qf.getSubformula());
					final Term negated = m_Script.quantifier(quantor, vars, body);
					super.convert(negated);
					return;
				}
				case PULL: {
					throw new UnsupportedOperationException(
							"cannot pull quantifier from negated formula");
				}
				default:
					throw new AssertionError("unknown quantifier handling");
				}
			} else {
				throw new UnsupportedOperationException("Unsupported " + notParam.getClass());
			}
		}
		
		private Term[] negateTerms(Term[] terms) {
			Term[] newTerms = new Term[terms.length];
			for (int i=0; i<terms.length; i++) {
				newTerms[i] = Util.not(m_Script, terms[i]);
			}
			return newTerms;
		}
		
		private Term[] negateLast(Term[] terms) {
			Term[] newTerms = new Term[terms.length];
			for (int i=0; i<terms.length-1; i++) {
				newTerms[i] = terms[i];
			}
			newTerms[terms.length-1] = Util.not(m_Script, terms[terms.length-1]);
			return newTerms;
		}
		
		private Term[] negateAllButLast(Term[] terms) {
			Term[] newTerms = new Term[terms.length];
			for (int i=0; i<terms.length-1; i++) {
				newTerms[i] = Util.not(m_Script, terms[i]);
			}
			newTerms[terms.length-1] = terms[terms.length-1];
			return newTerms;
		}

		
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			Term simplified = SmtUtils.termWithLocalSimplification(m_Script, 
					appTerm.getFunction().getName(), 
					appTerm.getFunction().getIndices(), newArgs);
			setResult(simplified);
		}

	}

}
