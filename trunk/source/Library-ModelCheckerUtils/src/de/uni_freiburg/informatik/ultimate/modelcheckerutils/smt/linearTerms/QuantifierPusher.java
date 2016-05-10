/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfDer;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;

/**
 * Transform a Term into form where quantifier are pushed as much inwards
 * as possible and quantifiers are eliminated via DER if possible
 * 
 * @author Matthias Heizmann
 * 
 */
public class QuantifierPusher extends TermTransformer {
	private final Script m_Script;
	private final IUltimateServiceProvider m_Services;
	private final IFreshTermVariableConstructor m_FreshTermVariableConstructor;

	public QuantifierPusher(Script script, IUltimateServiceProvider services, 
			IFreshTermVariableConstructor freshTermVariableConstructor) {
		m_Script = script;
		m_Services = services;
		m_FreshTermVariableConstructor = freshTermVariableConstructor;
	}

	@Override
	protected void convert(Term term) {
		if (term instanceof QuantifiedFormula) {
			final Term pushed = tryToPush((QuantifiedFormula) term); 
			super.convert(pushed);
		} else {
			super.convert(term);
		}
	}

	private Term tryToPush(QuantifiedFormula quantifiedFormula) {
		final Term subformula = quantifiedFormula.getSubformula();
		final Term result;
		if (subformula instanceof QuantifiedFormula) {
			QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) subformula;
			if (quantifiedSubFormula.getQuantifier() == quantifiedFormula.getQuantifier()) {
				QuantifiedFormula combined = sameQuantifier(quantifiedFormula, quantifiedSubFormula);
				result = tryToPush(combined);
			} else {
				result = otherQuantifier(quantifiedFormula, quantifiedSubFormula);
			}
		} else if (subformula instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) subformula;
			if (appTerm.getFunction().getApplicationString().equals("and")) {
				if (quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS) {
					result = otherFinite(quantifiedFormula, appTerm);
				} else {
					result = sameFinite(quantifiedFormula, appTerm);
				}
				
			} else if (appTerm.getFunction().getApplicationString().equals("or")) {
				if (quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS) {
					result = sameFinite(quantifiedFormula, appTerm);
				} else {
					result = otherFinite(quantifiedFormula, appTerm);
				}
			} else {
				result = quantifiedFormula;
			}
		} else {
			result = quantifiedFormula;
		}
		return result;
	}

	private Term sameFinite(QuantifiedFormula quantifiedFormula, ApplicationTerm appTerm) {
		Term[] oldParams = appTerm.getParameters();
		Term[] newParams = new Term[oldParams.length];
		for (int i=0; i<oldParams.length; i++) {
			newParams[i] = SmtUtils.quantifier(m_Script, quantifiedFormula.getQuantifier(), 
					Arrays.asList(quantifiedFormula.getVariables()), oldParams[i], 
					m_FreshTermVariableConstructor);
		}
		return m_Script.term(appTerm.getFunction().getName(), newParams);
	}

	private Term otherFinite(QuantifiedFormula quantifiedFormula, ApplicationTerm appTerm) {
		assert quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS && appTerm.getFunction().getName().equals("and")
				|| quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL && appTerm.getFunction().getName().equals("or");
//		{
//			// transform to DNF (resp. CNF)
//			appTerm = (ApplicationTerm) (new IteRemover(m_Script)).transform(appTerm);
//			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS) {
//				appTerm = (ApplicationTerm) (new Dnf(m_Script, m_Services, m_FreshTermVariableConstructor)).transform(appTerm);
//			} else if (quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL) {
//				appTerm = (ApplicationTerm) (new Cnf(m_Script, m_Services, m_FreshTermVariableConstructor)).transform(appTerm);
//			} else {
//				throw new AssertionError("unknown quantifier");
//			}
//		}
		final Term[] derResult;
		Set<TermVariable> eliminatees = new HashSet<TermVariable>(Arrays.asList(quantifiedFormula.getVariables()));
		{
			XnfDer xnfDer = new XnfDer(m_Script, m_Services, m_FreshTermVariableConstructor);
			Term[] xjuncts = PartialQuantifierElimination.getXjunctsInner(quantifiedFormula.getQuantifier(), appTerm);
			derResult = xnfDer.tryToEliminate(quantifiedFormula.getQuantifier(), xjuncts, eliminatees);
			if (eliminatees.isEmpty()) {
				Term result = PartialQuantifierElimination.composeXjunctsInner(
						m_Script, quantifiedFormula.getQuantifier(), derResult);
				return result;
			}
		} 
		HashRelation<TermVariable, Term> eliminatee2param = new HashRelation<>();
		for (Term xjunct : derResult) {
			for (TermVariable tv : xjunct.getFreeVars()) {
				if (eliminatees.contains(tv)) {
					eliminatee2param.addPair(tv, xjunct);
				}
			}
		}
		HashRelation<Term, TermVariable> xjunct2singleOccurrenceEliminatee = new HashRelation<>();
		List<TermVariable> multiOcucrrenceEliminatees = new ArrayList<>();
		for (TermVariable tv : eliminatee2param.getDomain()) {
			Set<Term> xjunctsOfTv = eliminatee2param.getImage(tv);
			if (xjunctsOfTv.size() == 1) {
				xjunct2singleOccurrenceEliminatee.addPair(xjunctsOfTv.iterator().next(), tv);
			} else if (xjunctsOfTv.isEmpty()) {
				throw new AssertionError("superficial var " + tv);
			} else {
				multiOcucrrenceEliminatees.add(tv);
			}
		}
		Term[] resultXjuncts = new Term[derResult.length];
		for (int i=0; i<derResult.length; i++) {
			if (xjunct2singleOccurrenceEliminatee.getDomain().contains(derResult[i])) {
				Set<TermVariable> vars = xjunct2singleOccurrenceEliminatee.getImage(derResult[i]);
				Term quantified = SmtUtils.quantifier(m_Script, quantifiedFormula.getQuantifier(), 
						vars, derResult[i], m_FreshTermVariableConstructor);
				resultXjuncts[i] = quantified;
			} else {
				resultXjuncts[i] = derResult[i];
			}
		}
		final Term resultXJunction = PartialQuantifierElimination.composeXjunctsInner(m_Script, 
				quantifiedFormula.getQuantifier(), resultXjuncts);
		final Term result = SmtUtils.quantifier(m_Script, quantifiedFormula.getQuantifier(), 
					multiOcucrrenceEliminatees, resultXJunction, m_FreshTermVariableConstructor);
		return result;
	}

	private Term otherQuantifier(QuantifiedFormula quantifiedFormula, QuantifiedFormula quantifiedSubFormula) {
		Term quantifiedSubFormulaPushed = (new QuantifierPusher(m_Script, m_Services, m_FreshTermVariableConstructor)).transform(quantifiedSubFormula);
		QuantifiedFormula update = (QuantifiedFormula) m_Script.quantifier(quantifiedFormula.getQuantifier(), quantifiedFormula.getVariables(), quantifiedSubFormulaPushed);
		if (quantifiedSubFormulaPushed instanceof QuantifiedFormula &&
				((QuantifiedFormula) quantifiedSubFormulaPushed).getQuantifier() == quantifiedSubFormula.getQuantifier()) {
			// cannot push
			return update;
		} else {
			// maybe we can push now
			return tryToPush(update);
		}
		
	}

	private QuantifiedFormula sameQuantifier(QuantifiedFormula quantifiedFormula, QuantifiedFormula quantifiedSubFormula) {
		assert (quantifiedSubFormula.getQuantifier() == quantifiedFormula.getQuantifier());
		assert (quantifiedSubFormula == quantifiedFormula.getSubformula());
		TermVariable[] vars;
		{
			TermVariable[] varsOuter = quantifiedFormula.getVariables();
			TermVariable[] varsInner = quantifiedSubFormula.getVariables();
			vars = Arrays.copyOf(varsOuter, varsOuter.length + varsInner.length);
			System.arraycopy(varsInner, 0, vars, varsOuter.length, varsInner.length);
		}
		Term body = quantifiedSubFormula.getSubformula();
		return (QuantifiedFormula) m_Script.quantifier(quantifiedFormula.getQuantifier(), vars, body);
	}

}
