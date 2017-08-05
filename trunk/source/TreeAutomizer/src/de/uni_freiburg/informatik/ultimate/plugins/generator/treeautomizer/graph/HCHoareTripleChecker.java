/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCOutVar;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;

/**
 * Wrapper for IHoareTripleCheckers that provides checking of Hoare triples we use in TreeAutomizer.
 * Hoare triples in TreeAutomizer have the form {/\ I_i(x)} F {I}, i.e., we have a set of preconditions,
 * a transition, and one postcondition. The predicates for the pre- and postconditions are HCPredicates,
 * the transition is given as a HornClause (which contains a HCTransformula).
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HCHoareTripleChecker {
	
	private final IHoareTripleChecker mHoareTripleChecker;
	private final PredicateUnifier mPredicateUnifier;
	private final HCPredicateFactory mPredicateFactory;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final ManagedScript mManagedScript;
	private final HCSymbolTable mSymbolTable;
	
	/**
	 * Constructor of HCHoareTripleChecker
	 * @param predicateUnifier Unifer for the predicates.
	 * @param cfgSmtToolkit 
	 * */
	public HCHoareTripleChecker(final PredicateUnifier predicateUnifier, final CfgSmtToolkit cfgSmtToolkit,
			final HCPredicateFactory predicateFactory, final HCSymbolTable symbolTable) {
		mPredicateUnifier = predicateUnifier;
		mHoareTripleChecker = new MonolithicHoareTripleChecker(cfgSmtToolkit);
		mPredicateFactory = predicateFactory;
		mCfgSmtToolkit = cfgSmtToolkit;
		mManagedScript = cfgSmtToolkit.getManagedScript();
		mSymbolTable = symbolTable;
	}
	

	/**
	 * Checks the validity of a Hoare triple that is given by a set of HCPredicates (precondition),
	 * a HornClause (action), and a single HCPredicate (postcondition).
	 * 
	 * @param preOld
	 * @param hornClause
	 * @param succ
	 * @return a Validity value for the Hoare triple
	 */
	public Validity check(List<IPredicate> preOld, HornClause hornClause, IPredicate succ) {
		/*
		 * sanitize pre
		 * -> for example if the HornClause not have any body predicates, just take "true" as precondition
		 */
		final List<IPredicate> pre;
		if (hornClause.getBodyPredicates().size() == 0) {
			assert preOld.isEmpty() || 
					(preOld.size() == 1 && preOld.get(0).getClosedFormula().toStringDirect().equals("true"));
			 pre = Collections.emptyList();
		} else {
			pre = preOld;
		}
//		
//		
//		assert pre.size() == hornClause.getNoBodyPredicates() : "The number of preconditions must match the number of "
//				+ "uninterpreted predicates in the Horn clause's body!";
		
		mManagedScript.lock(this);
		mManagedScript.push(this, 1);
		
//		/*
//		 * Compute the precondition
//		 *  - substitute the predicate formulas of the "pre" predicates
//		 *  - conjoin the substituted predicates
//		 */
//		final Term[] substitutedPredicateFormulas = new Term[pre.size()];
//		for (int predPos = 0; predPos < hornClause.getNoBodyPredicates(); predPos++) {
//			assert pre.get(predPos).getVars().size() == hornClause.getBodyPredicates().get(predPos).getArity();
//			final IPredicate currentPrePred = pre.get(predPos);
//
//			final Term substitutedFormula = substitutePredicateFormula(currentPrePred, 
//					hornClause.getProgramVarsForPredPos(predPos));
//			assert substitutedFormula != null;
//			assert substitutedFormula.getFreeVars().length == 0 : "formula should have been closed by substitution";
//			substitutedPredicateFormulas[predPos] = substitutedFormula;
//		}
//		
//		final Term preConditionFormula = Util.and(mManagedScript.getScript(), substitutedPredicateFormulas);
//		assert preConditionFormula.getFreeVars().length == 0 : "formula should have been closed by substitution";
//		
//		/*
//		 * Compute the postcondition
//		 */
//		final Term postConditionFormula = substitutePredicateFormula(succ, hornClause.getProgramVarsForHeadPred());
//		assert postConditionFormula.getFreeVars().length == 0 : "formula should have been closed by substitution";
//		final Term negatedPostConditionFormula = Util.not(mManagedScript.getScript(), postConditionFormula);

		Term preConditionFormula = mManagedScript.term(this, "true");
		
		for (int i = 0; i < pre.size(); i++) {
			final Term preCondConjunct = unify(pre.get(i), hornClause.getTermVariablesForPredPos(i));
			final Term closedPreCondConjunct = close(preCondConjunct, mSymbolTable);
			preConditionFormula = Util.and(mManagedScript.getScript(), preConditionFormula, closedPreCondConjunct);
		}
		mManagedScript.assertTerm(this, preConditionFormula);

		mManagedScript.assertTerm(this, close(hornClause.getFormula(), mSymbolTable));

		final Term negatedPostConditionFormula = SmtUtils.not(mManagedScript.getScript(),
				unify(succ, hornClause.getTermVariablesForHeadPred()));
		final Term closedNegatedPostConditionFormula = close(negatedPostConditionFormula, mSymbolTable);
		mManagedScript.assertTerm(this, closedNegatedPostConditionFormula);
		
		final LBool satResult = mManagedScript.checkSat(this);
		
		mManagedScript.pop(this, 1);
		mManagedScript.unlock(this);
		return IHoareTripleChecker.convertLBool2Validity(satResult);
	}


	private Term close(Term term, HCSymbolTable symbolTable) {
		final Map<Term, Term> substitution = new HashMap<>();
		
		for (TermVariable fv : term.getFreeVars()) {
			substitution.put(fv, symbolTable.getConstForTermVar(fv));
		}
		
		return new Substitution(mManagedScript, substitution).transform(term);
	}


	private Term unify(IPredicate iPredicate, List<TermVariable> termVariablesForPredPos) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (IProgramVar pvar : iPredicate.getVars()) {
			final HCOutVar hcvar = (HCOutVar) pvar;
			substitution.put(hcvar.getTermVariable(), termVariablesForPredPos.get(hcvar.getArgumentPos()));
		}
		return new Substitution(mManagedScript, substitution).transform(iPredicate.getFormula());
	}


//	private Term closeHcTransFormula(Term term) {
//		Map<Term, Term> substitution = new HashMap<>();
//		assert false;
////		for (Entry<IProgramVar, TermVariable> en : term.getInVars().entrySet()) {
////			substitution.put(en.getValue(), en.getKey().getDefaultConstant());
////		}
////		for (Entry<IProgramVar, TermVariable> en : term.getOutVars().entrySet()) {
////			substitution.put(en.getValue(), en.getKey().getDefaultConstant());
////		}
//		return new Substitution(mManagedScript, substitution).transform(term);
//	}


	/**
	 * Substitute the formula of an IPredicate over HCOutVars through a given list of ProgramVariabls (appearing in a
	 *  TransFormula)
	 * 
	 * @param predicate
	 * @param programVars
	 * @param predicateArity
	 * @return
	 */
	private Term substitutePredicateFormula(final IPredicate predicate, final List<IProgramVar> programVars) {
		int predicateArity = programVars.size();
		final Map<Integer, HCOutVar> sortedHCOutVars = sortHCOutVars(predicate);//predicate.getVars());
//		assert programVars.size() >= predicate.getVars().size();

		final Map<Term, Term> substitution = new HashMap<>();
		for (int argPos = 0; argPos < predicateArity; argPos++) {
			final HCOutVar predVarAtArgPos = sortedHCOutVars.get(argPos);
			if (predVarAtArgPos != null) {
				substitution.put(
//						sortedHCOutVars.get(argPos).getTermVariable(), 
						predVarAtArgPos.getTermVariable(), 
						programVars.get(argPos).getDefaultConstant());
			}
		}
		Term substitutedFormula = 
				new Substitution(mManagedScript, substitution).transform(predicate.getFormula());
		
		substitutedFormula = replaceFreeVarsWithFreshConstants(substitutedFormula);
		
		return substitutedFormula;
	}


	private Term replaceFreeVarsWithFreshConstants(Term formula) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (TermVariable fv : formula.getFreeVars()) {
			substitution.put(fv, 
					SmtUtils.buildNewConstant(mManagedScript.getScript(), fv.getName(), fv.getSort().getName()));
		}
		return new Substitution(mManagedScript, substitution).transform(formula);
	}


	private Map<Integer, HCOutVar> sortHCOutVars(IPredicate pred) {
		Map<Integer, HCOutVar> result = new HashMap<>();
		for (IProgramVar var : pred.getVars()) {
			final HCOutVar hcOutVar = (HCOutVar) var;
			result.put(hcOutVar.getArgumentPos(), hcOutVar);
		}
		return result;
	}


	public Validity check(TreeAutomatonRule<HornClause, IPredicate> rule) {
		return check(rule.getSource(), rule.getLetter(), rule.getDest());
	}
}
