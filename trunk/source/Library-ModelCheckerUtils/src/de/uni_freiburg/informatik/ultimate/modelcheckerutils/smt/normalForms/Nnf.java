package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;


/**
 * Transform Boolean Term into negation normal form.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class Nnf {
	
	protected final Script m_Script;
	private final NnfTransformerHelper m_NnfTransformerHelper;
	private List<List<TermVariable>> m_QuantifiedVariables;
	
	public Nnf(Script script, IUltimateServiceProvider services) {
		super();
		m_Script = script;
		m_NnfTransformerHelper = getNnfTransformerHelper(services);
		
	}
	
	protected NnfTransformerHelper getNnfTransformerHelper(IUltimateServiceProvider services) {
		return new NnfTransformerHelper(services);
	}
	
	public Term transform(Term term) {
		assert m_QuantifiedVariables == null;
		m_QuantifiedVariables = new ArrayList<List<TermVariable>>();
		List<TermVariable> firstQuantifierBlock = new ArrayList<TermVariable>();
		m_QuantifiedVariables.add(firstQuantifierBlock);
		Term result = m_NnfTransformerHelper.transform(term);
		for (int i=0; i<m_QuantifiedVariables.size(); i++) {
			TermVariable[] variables = m_QuantifiedVariables.get(i).toArray(new TermVariable[0]);
			if (variables.length > 0) {
				int quantor = i%2;
				assert QuantifiedFormula.EXISTS == 0;
				assert QuantifiedFormula.FORALL == 1;
				result = m_Script.quantifier(quantor, variables, result);
			}
		}
		assert (Util.checkSat(m_Script, m_Script.term("distinct", term, result)) != LBool.SAT);
		m_QuantifiedVariables = null;
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
					super.convert(term);
					return;
				} else if (functionName.equals("or")) {
					super.convert(term);
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
						SmtUtils.hasBooleanParams(appTerm)) {
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
				} else if (functionName.equals("distinct") && 
						SmtUtils.hasBooleanParams(appTerm)) {
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
						convert(SmtUtils.binaryBooleanInequality(
								m_Script, params[0], params[1]));
					}
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
				QuantifiedFormula qf = (QuantifiedFormula) term;
				List<TermVariable> variables;
				if (m_QuantifiedVariables.size()-1 == qf.getQuantifier()) {
					assert QuantifiedFormula.EXISTS == 0;
					assert QuantifiedFormula.FORALL == 1;
					variables = m_QuantifiedVariables.get(m_QuantifiedVariables.size()-1);
				} else {
					variables = new ArrayList<TermVariable>();
					m_QuantifiedVariables.add(variables);
				}
				Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
				for (TermVariable oldTv : qf.getVariables()) {
					TermVariable freshTv = oldTv.getTheory().createFreshTermVariable("nnf",oldTv.getSort());
					substitutionMapping.put(oldTv, freshTv);
					variables.add(freshTv);
				}
				Term newBody = (new SafeSubstitution(m_Script, substitutionMapping)).transform(qf.getSubformula());
				// we deliberately call convert() instead of super.convert()
				// the argument of this call might have been simplified
				// to a term whose function symbol is neither "and" nor "or"
				convert(newBody);
				return;
			} else {
				throw new UnsupportedOperationException("Unsupported " + term.getClass());
			}
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
						SmtUtils.hasBooleanParams(appTerm)) {
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
						convert(SmtUtils.binaryBooleanInequality(
								m_Script, notParams[0], notParams[1]));
					}
				} else if (functionName.equals("distinct") && 
						SmtUtils.hasBooleanParams(appTerm)) {
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
				throw new UnsupportedOperationException(
						"NNF transformation does not support QuantifiedFormula");
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

	}

}
