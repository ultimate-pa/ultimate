package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class XnfIrd extends XjunctPartialQuantifierElimination {

	public XnfIrd(Script script, IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "infinity restrictor drop";
	}

	@Override
	public String getAcronym() {
		return "IRD";
	}

	@Override
	public Term[] tryToEliminate(int quantifier, Term[] oldParams,
			Set<TermVariable> eliminatees) {
		Iterator<TermVariable> it = eliminatees.iterator();
		Term[] result = oldParams;
		while (it.hasNext()) {
			TermVariable tv = it.next();
			if (!SmtUtils.getFreeVars(Arrays.asList(result)).contains(tv)) {
				// case where var does not occur
				it.remove();
				continue;
			} else {
				if (tv.getSort().isNumericSort()) {
					Term[] withoutTv = irdSimple(m_Script, quantifier, result, tv, m_Logger);
					if (withoutTv != null) {
						m_Logger.debug(new DebugMessage("eliminated quantifier via IRD for {0}", tv));
						result = withoutTv;
						it.remove();
					} else {
						m_Logger.debug(new DebugMessage("not eliminated quantifier via IRD for {0}", tv));
					}
				} else {
					// ird is only applicable to variables of numeric sort
					m_Logger.debug(new DebugMessage("not eliminated quantifier via IRD for {0}", tv));
				}
			}
		}
		return result;
	}
	
	/**
	 * If the application term contains only parameters param such that for each
	 * param one of the following holds and the third case applies at most once,
	 * we return all params that do not contain tv. 1. param does not contain tv
	 * 2. param is an AffineRelation such that tv is a variable of the
	 * AffineRelation and the function symbol is "distinct" and quantifier is ∃
	 * or the function symbol is "=" and the quantifier is ∀ 3. param is an
	 * inequality
	 * 
	 * @param logger
	 */
	public static Term[] irdSimple(Script script, int quantifier, Term[] oldParams, TermVariable tv, Logger logger) {
		assert tv.getSort().isNumericSort() : "only applicable for numeric sorts";

		ArrayList<Term> paramsWithoutTv = new ArrayList<Term>();
		short inequalitiesWithTv = 0;
		for (Term oldParam : oldParams) {
			if (!Arrays.asList(oldParam.getFreeVars()).contains(tv)) {
				paramsWithoutTv.add(oldParam);
			} else {
				AffineRelation affineRelation;
				try {
					affineRelation = new AffineRelation(oldParam);
				} catch (NotAffineException e) {
					// unable to eliminate quantifier
					return null;
				}
				if (!affineRelation.isVariable(tv)) {
					// unable to eliminate quantifier
					// tv occurs in affine relation but not as affine variable
					// it might occur inside a function or array.
					return null;
				}
				try {
					affineRelation.onLeftHandSideOnly(script, tv);
				} catch (NotAffineException e) {
					// unable to eliminate quantifier
					return null;
				}
				String functionSymbol = affineRelation.getFunctionSymbolName();
				switch (functionSymbol) {
				case "=":
					if (quantifier == QuantifiedFormula.EXISTS) {
						// unable to eliminate quantifier
						return null;
					} else if (quantifier == QuantifiedFormula.FORALL) {
						// we may drop this parameter
					} else {
						throw new AssertionError("unknown quantifier");
					}
					break;
				case "distinct":
					if (quantifier == QuantifiedFormula.EXISTS) {
						// we may drop this parameter
					} else if (quantifier == QuantifiedFormula.FORALL) {
						// unable to eliminate quantifier
						return null;
					} else {
						throw new AssertionError("unknown quantifier");
					}
					break;
				case ">":
				case ">=":
				case "<":
				case "<=":
					if (inequalitiesWithTv > 0) {
						// unable to eliminate quantifier, we may drop at most
						// one inequality
						return null;
					} else {
						inequalitiesWithTv++;
						// we may drop this parameter (but it has to be the
						// only dropped inequality
					}
					break;
				default:
					throw new AssertionError("unknown functionSymbol");
				}
			}
		}
		return paramsWithoutTv.toArray(new Term[paramsWithoutTv.size()]);
	}

}
