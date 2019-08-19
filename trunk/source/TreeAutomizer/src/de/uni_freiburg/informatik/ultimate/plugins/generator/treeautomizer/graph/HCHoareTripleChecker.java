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
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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

	private final PredicateUnifier mPredicateUnifier;
	private final ManagedScript mManagedScript;
	private final HcSymbolTable mSymbolTable;

	/**
	 * Constructor of HCHoareTripleChecker
	 * @param predicateUnifier Unifier for the predicates.
	 * @param cfgSmtToolkit
	 * */
	public HCHoareTripleChecker(final PredicateUnifier predicateUnifier, //final CfgSmtToolkit cfgSmtToolkit,
			final ManagedScript mgdScript, final HcSymbolTable symbolTable) {
		mPredicateUnifier = predicateUnifier;
		mManagedScript = mgdScript;
		mSymbolTable = symbolTable;
	}


	/**
	 *
	 * Substitute HcHeadVars according to bodyPredArgs of hornclause (in particular their default constants), in pre
	 * predicates, assert them.
	 *
	 * @param pre preState predicates, still in terms of HcHeadVars
	 * @param hornClause
	 * @return
	 */
	private void assertPreconditions(final List<IPredicate> pre, final HornClause hornClause) {
		mManagedScript.echo(this, new QuotedObject("starting Hoare triple check"));

		for (int bodyComponentIndex = 0; bodyComponentIndex < pre.size(); bodyComponentIndex++) {
			mManagedScript.echo(this, new QuotedObject("asserting body component nr " + bodyComponentIndex + ":"));

			final Map<Term, Term> subs = new HashMap<>();
			final IPredicate currentPre = pre.get(bodyComponentIndex);
			for (final TermVariable freeVar : currentPre.getFormula().getFreeVars()) {
				final HcHeadVar headVar = (HcHeadVar) mSymbolTable.getProgramVar(freeVar);
				final Term bodyArg = hornClause.getBodyPredToArgs().get(bodyComponentIndex).get(headVar.getIndex());
				subs.put(headVar.getTermVariable(), bodyArg);
			}

			final Term preCondConjunct = new Substitution(mManagedScript, subs).transform(currentPre.getFormula());
			final Term closedPreCondConjunct = close(preCondConjunct);
			mManagedScript.assertTerm(this, closedPreCondConjunct);
		}
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
	public Validity check(final List<IPredicate> preOld, final HornClause hornClause, final IPredicate succ) {

		/* precondition */
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

		mManagedScript.lock(this);
		mManagedScript.push(this, 1);

		assertPreconditions(pre, hornClause);

		/* constraint */
		mManagedScript.echo(this, new QuotedObject("asserting horn clause constraint: "));
		final Term closedConstraint = close(hornClause.getConstraintFormula());
		mManagedScript.assertTerm(this, closedConstraint);

		/* postcondition */
		// the postcondition can keeps its head vars, as the Hornclause did
		mManagedScript.echo(this, new QuotedObject("asserting negated post condition: "));
		final Term closedNegatedPostConditionFormula = SmtUtils.not(mManagedScript.getScript(),
				succ.getClosedFormula());
		mManagedScript.assertTerm(this, closedNegatedPostConditionFormula);

		final LBool satResult = mManagedScript.checkSat(this);

		mManagedScript.echo(this, new QuotedObject("finishing Hoare triple check"));
		mManagedScript.pop(this, 1);
		mManagedScript.unlock(this);
		return IHoareTripleChecker.convertLBool2Validity(satResult);
	}


	private Term close(final Term term) {
		final Map<Term, Term> substitution = new HashMap<>();

		for (final TermVariable fv : term.getFreeVars()) {
			final IProgramVar pv = mSymbolTable.getProgramVar(fv);
			substitution.put(fv, pv.getDefaultConstant());
		}

		return new Substitution(mManagedScript, substitution).transform(term);
	}

	public Validity check(final TreeAutomatonRule<HornClause, IPredicate> rule) {
		return check(rule.getSource(), rule.getLetter(), rule.getDest());
	}

	public IPredicate getFalsePredicate() {
		return mPredicateUnifier.getFalsePredicate();
	}
}
