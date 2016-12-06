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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XjunctPartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.XnfDer;

/**
 * Transform a Term into form where quantifier are pushed as much inwards
 * as possible and quantifiers are eliminated via DER if possible
 * 
 * @author Matthias Heizmann
 * 
 */
public class QuantifierPusher extends TermTransformer {
	
	private enum SubformulaClassification { 
		CORRESPODING_FINITE_CONNECTIVE,
		DUAL_FINITE_CONNECTIVE,
		SAME_QUANTIFIER,
		DUAL_QUANTIFIER,
		ATOM,
	}
	
	private final Script mScript;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;

	public QuantifierPusher(final ManagedScript script, final IUltimateServiceProvider services) {
		mServices = services;
		mMgdScript = script;
		mScript = script.getScript();
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			final Term termToRecurseOn = tryToPush(quantifiedFormula);
			super.convert(termToRecurseOn);
		} else {
			super.convert(term);
		}
	}

	private Term tryToPush(QuantifiedFormula quantifiedFormula) throws AssertionError {
		SubformulaClassification classification = classify(quantifiedFormula.getQuantifier(), quantifiedFormula.getSubformula());
		if (classification == SubformulaClassification.DUAL_QUANTIFIER) {
			quantifiedFormula = processDualQuantifier(quantifiedFormula);
			classification = classify(quantifiedFormula.getQuantifier(), quantifiedFormula.getSubformula());
		}
		while (classification == SubformulaClassification.SAME_QUANTIFIER) {
			quantifiedFormula = processSameQuantifier(quantifiedFormula);
			classification = classify(quantifiedFormula.getQuantifier(), quantifiedFormula.getSubformula());
		}
		Term termToRecurseOn;
		switch (classification) {
		case ATOM:
			termToRecurseOn = quantifiedFormula;
			break;
		case CORRESPODING_FINITE_CONNECTIVE:
			termToRecurseOn = pushOverCorrespondingFiniteConnective(quantifiedFormula);
			break;
		case DUAL_FINITE_CONNECTIVE:
			termToRecurseOn = tryToPushOverDualFiniteConnective(quantifiedFormula);
			break;
		case DUAL_QUANTIFIER:
			throw new AssertionError("must have been handled above");
		case SAME_QUANTIFIER:
			throw new AssertionError("must have been handled above");
		default:
			throw new AssertionError("unknown value " + classification);
		}
		return termToRecurseOn;
	}

	private Term pushOverCorrespondingFiniteConnective(final QuantifiedFormula quantifiedFormula) {
		assert (quantifiedFormula.getSubformula() instanceof ApplicationTerm);
		final ApplicationTerm appTerm = (ApplicationTerm) quantifiedFormula.getSubformula();
		assert (appTerm.getFunction().getApplicationString().equals(
				SmtUtils.getCorrespondingFiniteConnective(quantifiedFormula.getQuantifier())));
		final Term[] oldParams = appTerm.getParameters();
		final Term[] newParams = new Term[oldParams.length];
		for (int i=0; i<oldParams.length; i++) {
			newParams[i] = SmtUtils.quantifier(mScript, quantifiedFormula.getQuantifier(), 
					Arrays.asList(quantifiedFormula.getVariables()), oldParams[i]);
		}
		return mScript.term(appTerm.getFunction().getName(), newParams);
	}

	private Term tryToPushOverDualFiniteConnective(final QuantifiedFormula quantifiedFormula) {
		assert (quantifiedFormula.getSubformula() instanceof ApplicationTerm);
		final ApplicationTerm appTerm = (ApplicationTerm) quantifiedFormula.getSubformula();
		assert (appTerm.getFunction().getApplicationString().equals(
				SmtUtils.getCorrespondingFiniteConnective(SmtUtils.getOtherQuantifier(quantifiedFormula.getQuantifier()))));

		assert quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS && appTerm.getFunction().getName().equals("and")
				|| quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL && appTerm.getFunction().getName().equals("or");
		
		// Step 1:
		// do partition
		// if you can push something, push and return
		// if you cannot push, continue
		final ParameterPartition pp = new ParameterPartition(mScript, quantifiedFormula);
		if (!pp.isIsPartitionTrivial()) {
			return pp.getTermWithPushedQuantifier();
		}
		
		// 2016-12-03 Matthias: plan for refactoring
		//
		// do partition
		// if you can push something, push and return
		// if you cannot push, continue
		//  
		// apply sequence of eliminations
		// after each, check topmost connector
		// if 'other finite' continue
		// else push (if possible) and return
		//
		// if all elimination processed (and still 'other finite')
		// check for 'same finite' in one 'other finite'
		// if exists, distribute, apply new pusher to result
		//            if less quantified return result
		//            if not less quantified return term after elimination
		// if not exists return
		
//		{
//			// transform to DNF (resp. CNF)
//			appTerm = (ApplicationTerm) (new IteRemover(mScript)).transform(appTerm);
//			if (quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS) {
//				appTerm = (ApplicationTerm) (new Dnf(mScript, mServices, mFreshTermVariableConstructor)).transform(appTerm);
//			} else if (quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL) {
//				appTerm = (ApplicationTerm) (new Cnf(mScript, mServices, mFreshTermVariableConstructor)).transform(appTerm);
//			} else {
//				throw new AssertionError("unknown quantifier");
//			}
//		}
		final Term[] derResult;
		final Set<TermVariable> eliminatees = new HashSet<TermVariable>(Arrays.asList(quantifiedFormula.getVariables()));
		{
			final int numberOfEliminateesBefore = eliminatees.size();
			final XjunctPartialQuantifierElimination xnfDer = new XnfDer(mMgdScript, mServices);
			final Term[] xjuncts = PartialQuantifierElimination.getXjunctsInner(quantifiedFormula.getQuantifier(), appTerm);
			derResult = xnfDer.tryToEliminate(quantifiedFormula.getQuantifier(), xjuncts, eliminatees);
			final Term result = PartialQuantifierElimination.applyDualFiniteConnective(
					mScript, quantifiedFormula.getQuantifier(), Arrays.asList(derResult));
			if (eliminatees.isEmpty()) {
				return result;
			}
			if (numberOfEliminateesBefore > eliminatees.size()) {
				// something was removed
				final QuantifiedFormula intermediate = (QuantifiedFormula) SmtUtils.quantifier(mScript, quantifiedFormula.getQuantifier(), eliminatees, result);
				return tryToPush(intermediate);
			}
			return SmtUtils.quantifier(mScript, quantifiedFormula.getQuantifier(), eliminatees, result);
		} 

	}

	private SubformulaClassification classify(final int quantifier, final Term subformula) {
		if (subformula instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) subformula;
			if (quantifiedSubFormula.getQuantifier() == quantifier) {
				return SubformulaClassification.SAME_QUANTIFIER;
			} else {
				return SubformulaClassification.DUAL_QUANTIFIER;
			}
		} else if (subformula instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) subformula;
			final String correspondingFiniteConnective = SmtUtils.getCorrespondingFiniteConnective(quantifier);
			if (appTerm.getFunction().getApplicationString().equals(correspondingFiniteConnective)) {
				return SubformulaClassification.CORRESPODING_FINITE_CONNECTIVE;
			}
			final String dualFiniteConnective = SmtUtils.getCorrespondingFiniteConnective(SmtUtils.getOtherQuantifier(quantifier));
			if (appTerm.getFunction().getApplicationString().equals(dualFiniteConnective)) {
				return SubformulaClassification.DUAL_FINITE_CONNECTIVE;
			}
			return SubformulaClassification.ATOM;
		} else {
			return SubformulaClassification.ATOM;
		}
	}
	
	private QuantifiedFormula processSameQuantifier(final QuantifiedFormula quantifiedFormula) {
		assert (quantifiedFormula.getSubformula() instanceof QuantifiedFormula);
		final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) quantifiedFormula.getSubformula();
		assert (quantifiedSubFormula.getQuantifier() == quantifiedFormula.getQuantifier());
		TermVariable[] vars;
		{
			final TermVariable[] varsOuter = quantifiedFormula.getVariables();
			final TermVariable[] varsInner = quantifiedSubFormula.getVariables();
			vars = Arrays.copyOf(varsOuter, varsOuter.length + varsInner.length);
			System.arraycopy(varsInner, 0, vars, varsOuter.length, varsInner.length);
		}
		final Term body = quantifiedSubFormula.getSubformula();
		return (QuantifiedFormula) mScript.quantifier(quantifiedFormula.getQuantifier(), vars, body);
	}
	
	private QuantifiedFormula processDualQuantifier(final QuantifiedFormula quantifiedFormula) {
		assert (quantifiedFormula.getSubformula() instanceof QuantifiedFormula);
		final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) quantifiedFormula.getSubformula();
		assert (quantifiedSubFormula.getQuantifier() == SmtUtils.getOtherQuantifier(quantifiedFormula.getQuantifier()));
		final Term quantifiedSubFormulaPushed = (new QuantifierPusher(mMgdScript, mServices)).transform(quantifiedSubFormula);
		final QuantifiedFormula update = (QuantifiedFormula) mScript.quantifier(quantifiedFormula.getQuantifier(), quantifiedFormula.getVariables(), quantifiedSubFormulaPushed);
		return update;
	}
}
