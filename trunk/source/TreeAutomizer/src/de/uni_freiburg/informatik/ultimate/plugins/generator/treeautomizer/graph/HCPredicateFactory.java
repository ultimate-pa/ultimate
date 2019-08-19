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
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * A factory for HornClause Predicates.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 */
public class HCPredicateFactory extends BasicPredicateFactory {

	private final ManagedScript mMgdScript;
	private final HCPredicate mDontCareLocationPredicate;
	private final HCPredicate mTrueLocationPredicate;
	private final HCPredicate mFalseLocationPredicate;
	private final HcSymbolTable mHCSymbolTable;

	private final Map<HcPredicateSymbol, HCPredicate> mLocToTruePred;

	/**
	 * The constructor of HornClause Factory
	 *
	 * @param services
	 * @param mgdScript
	 * @param symbolTable
	 * @param simplificationTechnique
	 * @param xnfConversionTechnique
	 */
	public HCPredicateFactory(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final HcSymbolTable symbolTable,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		super(services, mgdScript, symbolTable);
		mMgdScript = mgdScript;
		mHCSymbolTable = symbolTable;

		mLocToTruePred = new HashMap<>();

		mDontCareLocationPredicate = newPredicate(symbolTable.getDontCareHornClausePredicateSymbol(),
				super.getDontCareTerm(), Collections.emptyList());
		mFalseLocationPredicate = getTruePredicateWithLocation(symbolTable.getFalseHornClausePredicateSymbol());
		mTrueLocationPredicate = getTruePredicateWithLocation(symbolTable.getTrueHornClausePredicateSymbol());
	}

	/**
	 * Create a True predicate with symbol.
	 *
	 * @param headPredicate
	 *            The given symbol
	 * @return The new true HCPredicate
	 */
	public HCPredicate getTruePredicateWithLocation(final HcPredicateSymbol headPredicate) {
		HCPredicate result = mLocToTruePred.get(headPredicate);
		if (result == null) {
			mMgdScript.lock(this);
			result = newPredicate(headPredicate, mMgdScript.term(this, "true"), Collections.emptyList());
			mMgdScript.unlock(this);
			mLocToTruePred.put(headPredicate, result);
		}
		return result;
	}

	public HCPredicate getTrueLocationPredicate() {
		return mTrueLocationPredicate;
	}

	public HCPredicate getFalseLocationPredicate() {
		return mFalseLocationPredicate;
	}

	public HCPredicate getDontCareLocationPredicate() {
		return mDontCareLocationPredicate;
	}

	public HCPredicate newPredicate(final HcPredicateSymbol loc, final Term term,
			final List<TermVariable> vars) {
		return newPredicate(Collections.singleton(loc), term, vars);
	}

	public HCPredicate newPredicate(final Set<HcPredicateSymbol> loc, final Term term, final List<TermVariable> vars) {
		final ComputeHcOutVarsAndNormalizeTerm chovant = new ComputeHcOutVarsAndNormalizeTerm(term, vars);

		final int finalSerialNumber = constructFreshSerialNumber();
		return new HCPredicate(loc, finalSerialNumber, chovant.getNormalizedTerm(), chovant.getProgramVars(),
				computeClosedFormula(chovant.getNormalizedTerm()), vars);
	}

	/***
	 * Create a new HCPredicate from a predicate symbol and the formulas.
	 *
	 * @param sym
	 *            The predicate symbol
	 * @param term
	 *            The formula of the predicate
	 * @param vars
	 * @return
	 *//*
	public HCPredicate newHCPredicate(final Set<HornClausePredicateSymbol> sym, final Term term,
			final List<TermVariable> vars) {
		return newPredicate(sym, term, vars);
	}*/

//	@Override
//	protected TermVarsProc constructTermVarsProc(final Term term) {
//		throw new UnsupportedOperationException("concept of TermVarsProc does not apply for Chc problem");
//	}

	private Term computeClosedFormula(final Term formula) {
		if (isDontCare(formula)) {
			return formula;
		}

		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final TermVariable fv : formula.getFreeVars()) {
			final ApplicationTerm defaultConstantForFv = mSymbolTable.getProgramVar(fv).getDefaultConstant();
			substitutionMapping.put(fv, defaultConstantForFv);
		}
		return new Substitution(mMgdScript, substitutionMapping).transform(formula);
	}

	/**
	 * When we construct a HCPredicate from a formula, then there are two cases:
	 * - the formula is already normalized, i.e., each of its free .. TODO..
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	class ComputeHcOutVarsAndNormalizeTerm {
		private final Term mNormalizedTerm;
		private final Set<IProgramVar> mProgramVars;

		public ComputeHcOutVarsAndNormalizeTerm(final Term formula, final List<TermVariable> variables) {
			if (isDontCare(formula)) {
				mNormalizedTerm = formula;
				mProgramVars = Collections.emptySet();
			} else {
//				final Map<Term, Term> normalizingSubstitution = new HashMap<>();
//				final Set<IProgramVar> hcOutVars = new HashSet<>();

//				for (int i = 0; i < variables.size(); i++) {
//					final HcBodyVar hcOutVar = mHCSymbolTable.getOrConstructHCOutVar(i, variables.get(i).getSort());
//					hcOutVars.add(hcOutVar);
//					normalizingSubstitution.put(variables.get(i), hcOutVar.getTermVariable());
//				}

//				mNormalizedTerm = new Substitution(mScript, normalizingSubstitution).transform(formula);
//				mProgramVars = hcOutVars;

				// TODO: make nicer, this may not need an extra class..
				mNormalizedTerm = formula;
				mProgramVars = variables.stream().map(tv -> mHCSymbolTable.getProgramVar(tv))
						.collect(Collectors.toSet());
			}
		}

		public Term getNormalizedTerm() {
			return mNormalizedTerm;
		}

		public Set<IProgramVar> getProgramVars() {
			return mProgramVars;
		}
	}
}
