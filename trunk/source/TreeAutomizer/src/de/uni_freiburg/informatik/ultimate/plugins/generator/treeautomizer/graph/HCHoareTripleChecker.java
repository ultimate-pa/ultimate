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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCOutVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
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
	 * @param pre
	 * @param hornClause
	 * @param succ
	 * @return a Validity value for the Hoare triple
	 */
	public Validity check(List<IPredicate> pre, HornClause hornClause, IPredicate succ) {
		assert pre.size() == hornClause.getNoBodyPredicates();
		
		mManagedScript.lock(this);
		mManagedScript.push(this, 1);
		
		/*
		 * Compute the precondition
		 *  - substitute the predicate formulas of the "pre" predicates
		 *  - conjoin the substituted predicates
		 */
		final Term[] substitutedPredicateFormulas = new Term[pre.size()];
		for (int predPos = 0; predPos < hornClause.getNoBodyPredicates(); predPos++) {
			assert pre.get(predPos).getVars().size() == hornClause.getBodyPredicates().get(predPos).getArity();
			final IPredicate currentPrePred = pre.get(predPos);

			final Term substitutedFormula = substitutePredicateFormula(currentPrePred, 
					hornClause.getProgramVarsForPredPos(predPos));
			substitutedPredicateFormulas[predPos] = substitutedFormula;
		}
		
		final Term preConditionFormula = Util.and(mManagedScript.getScript(), substitutedPredicateFormulas);
		
		/*
		 * Compute the postcondition
		 */
		final Term postConditionFormula = substitutePredicateFormula(succ, hornClause.getProgramVarsForHeadPred());

		mManagedScript.assertTerm(this, preConditionFormula);
		mManagedScript.assertTerm(this, hornClause.getTransformula().getClosedFormula());
		mManagedScript.assertTerm(this, postConditionFormula);
		
		final LBool satResult = mManagedScript.checkSat(this);
		
		mManagedScript.pop(this, 1);
		mManagedScript.unlock(this);
		return IHoareTripleChecker.convertLBool2Validity(satResult);
	}


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
		final List<HCOutVar> sortedHCOutVars = sortHCOutVars(predicate.getVars());
		assert sortedHCOutVars.size() == predicateArity;

		final Map<Term, Term> substitution = new HashMap<>();
		for (int argPos = 0; argPos < predicateArity; argPos++) {
			substitution.put(
					sortedHCOutVars.get(argPos).getTermVariable(), 
					programVars.get(argPos).getDefaultConstant());
		}
		final Term substitutedFormula = 
				new Substitution(mManagedScript, substitution).transform(predicate.getFormula());
		return substitutedFormula;
	}


	private List<HCOutVar> sortHCOutVars(Set<IProgramVar> vars) {
		TreeSet<HCOutVar> treeSet = new TreeSet<>();
		treeSet.addAll(vars.stream().map(v -> ((HCOutVar) v)).collect(Collectors.toSet()));
		return new ArrayList<HCOutVar>(treeSet);
	}
}
