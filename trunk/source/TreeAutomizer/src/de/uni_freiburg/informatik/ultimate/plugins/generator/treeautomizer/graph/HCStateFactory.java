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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class HCStateFactory implements IMergeStateFactory<HCPredicate> {

	// final protected boolean mComputeHoareAnnotation;
	// final protected TAPreferences mPref;
	private final HCPredicate mEmtpyStack;

	private final ManagedScript mBackendSmtSolverScript;
	private final SimplifyDDA mSimplifier;
	private final TermTransferrer mTermTransferrer;
	private final boolean mTransferToScriptNeeded;

	private final HCPredicateFactory mPredicateFactory;

	public HCStateFactory(final ManagedScript backendSmtSolverScript, final HCPredicateFactory predicateFactory,
			final HCSymbolTable symbolTable) {
		mBackendSmtSolverScript = backendSmtSolverScript;

		mEmtpyStack = predicateFactory.getDontCarePredicate();

		mTermTransferrer = new TermTransferrer(mBackendSmtSolverScript.getScript());
		mTransferToScriptNeeded = true;
		mSimplifier = new SimplifyDDA(mBackendSmtSolverScript.getScript());
		mPredicateFactory = predicateFactory;
	}



	private HCPredicate reduceFormula(final HCPredicate[] preds, final boolean andOp) {
		// TODO: Check hashing of TermVariable and HCVar.
	
		final Set<IProgramVar> progVars = new HashSet<>();
		final Map<Term, HCVar> varsMap = new HashMap<>();

		final Term[] terms = new Term[preds.length];
		final Map<String, Term> invMap = new HashMap<>();
		for (int i = 0; i < preds.length; ++i) {
			final Map<Term, Term> substMap = new HashMap<>();
			for (final Entry<Term, HCVar> v : preds[i].getVarsMap().entrySet()) {
				if (invMap.containsKey(v.getValue().getGloballyUniqueId())) {
					substMap.put(v.getKey(), invMap.get(v.getValue().getGloballyUniqueId()));
				} else {
					invMap.put(v.getValue().getGloballyUniqueId(), v.getKey());
				}
			}
			final Substitution subst = new Substitution(mBackendSmtSolverScript, substMap);
			terms[i] = subst.transform(preds[i].getFormula());
		}

		final HornClausePredicateSymbol loc = preds[0].mProgramPoint;

		int predHash = HashUtils.hashHsieh(mBackendSmtSolverScript.hashCode(), loc, preds);
		for (final HCPredicate p : preds) {
			predHash = HashUtils.hashHsieh(mBackendSmtSolverScript.hashCode(), predHash, p, p.mProgramPoint);
		}
		final Term formula = mSimplifier.getSimplifiedTerm(
				andOp ? Util.and(mBackendSmtSolverScript.getScript(), terms) :
					Util.or(mBackendSmtSolverScript.getScript(), terms));
		
		final Set<String> prodVars = new HashSet<>();
		for (final TermVariable var : formula.getFreeVars()) {
			prodVars.add(var.toString());
		}

		for (int i = 0; i < preds.length; ++i) {
			for (final Entry<Term, HCVar> v : preds[i].getVarsMap().entrySet()) {
				if (prodVars.contains(v.getValue().getTermVariable().toString())) {
					varsMap.put(v.getKey(), v.getValue());
					progVars.add(v.getValue());
				}
			}
		}
		
		return mPredicateFactory.newPredicate(loc, predHash, formula, progVars, varsMap);
	}
	
	@Override
	public HCPredicate intersection(final HCPredicate p1, final HCPredicate p2) {
		return reduceFormula(new HCPredicate[]{p1, p2}, true);
	}

	@Override
	public HCPredicate merge(final Collection<HCPredicate> states) {
		return reduceFormula(states.toArray(new HCPredicate[]{}), false);
	}

	public boolean isSatisfiable(final List<HCPredicate> src, final HornClause pf, final HCPredicate dest) {
		mBackendSmtSolverScript.lock(this);
		for (final HCPredicate pSrc : src) {
			for (final IProgramVar v : pSrc.getVars()) {
				if (!pf.getTransformula().getInVars().containsKey(v)) {
					return false;
				}
			}
		}
		for (final IProgramVar v : dest.getVars()) {
			if (!pf.getTransformula().getOutVars().containsKey(v)) {
				return false;
			}
		}
		mBackendSmtSolverScript.push(this, 1);
		final Term[] terms = new Term[src.size()];
		//System.err.println("Check: " + src + " " + pf + " " + dest);
		for (int i = 0; i < src.size(); ++i) {
			final Map<Term, Term> substMap = new HashMap<>();
			for (final IProgramVar v : src.get(i).getVars()) {
				substMap.put(v.getTermVariable(), pf.getTransformula().getInVars().get(v));
			}
			final Substitution subst = new Substitution(mBackendSmtSolverScript, substMap);
			terms[i] = subst.transform(src.get(i).getFormula());
			//System.err.println("src: " + src.get(i).getFormula() + " " + substMap);
		}
		final Map<Term, Term> substMap = new HashMap<>();
		for (final IProgramVar v : dest.getVars()) {
			substMap.put(v.getTermVariable(), pf.getTransformula().getOutVars().get(v));
		}
		//System.err.println(dest.getFormula() + " " + substMap);
		//System.err.println(pf);
		//System.err.println();
		final Substitution subst = new Substitution(mBackendSmtSolverScript, substMap);
		
		final Term A = Util.and(mBackendSmtSolverScript.getScript(), terms);
		final Term S = transferToCurrentScriptIfNecessary(pf.getTransformula().getFormula());
		final Term B = subst.transform(dest.getFormula());
		
		final Term T = mSimplifier.getSimplifiedTerm(Util.and(mBackendSmtSolverScript.getScript(), new Term[]{A, S, Util.not(mBackendSmtSolverScript.getScript(), B)}));
		//System.err.println(T);
		//System.err.print(A + " o " + S + " ==> " + B);// + " :: " + (result == LBool.SAT));
		if (T.getFreeVars().length > 0) {
			//System.err.println(":: non-sat");
			mBackendSmtSolverScript.unlock(this);
			return false;
		}
		mBackendSmtSolverScript.assertTerm(this, T);
		final LBool result = mBackendSmtSolverScript.checkSat(this);
		
		mBackendSmtSolverScript.pop(this, 1);
		//System.err.println(result != LBool.SAT ? ":=: sat" : ":=: non-sat");
		//return false;
		mBackendSmtSolverScript.unlock(this);
		return result != LBool.SAT;
		
	}

	private TermVariable transferToCurrentScriptIfNecessary(final TermVariable tv) {
		final TermVariable result;
		if (mTransferToScriptNeeded) {
			result = (TermVariable) mTermTransferrer.transform(tv);
		} else {
			result = tv;
		}
		return result;
	}

	private Term transferToCurrentScriptIfNecessary(final Term term) {
		final Term result;
		if (mTransferToScriptNeeded) {
			result = mTermTransferrer.transform(term);
		} else {
			result = term;
		}
		return result;
	}
	
	@Override
	public HCPredicate createEmptyStackState() {
		return mEmtpyStack;
	}
}