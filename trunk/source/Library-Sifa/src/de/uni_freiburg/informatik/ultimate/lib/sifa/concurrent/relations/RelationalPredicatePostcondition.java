/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class RelationalPredicatePostcondition {

	public static record PreparedRelation(IPredicate relation, Set<TermVariable> preVarsToProject,
			Map<Term, Term> primedToUnprimed) {
		public PreparedRelation {
			preVarsToProject = Set.copyOf(preVarsToProject);
			primedToUnprimed = Map.copyOf(primedToUnprimed);
		}
	}

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final PrimedDefaultIcfgSymbolTable mSymbolTable;
	private final boolean mProjectAllGlobalPreVars;
	private final Set<TermVariable> mAllGlobalPreVarsToProject;
	private final Map<Term, Term> mAllGlobalPrimedToUnprimed;
	private SifaStats mStats;

	public RelationalPredicatePostcondition(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable) {
		this(services, managedScript, predicateFactory, symbolTable, false);
	}

	public RelationalPredicatePostcondition(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable,
			final boolean projectAllGlobalPreVars) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
		mProjectAllGlobalPreVars = projectAllGlobalPreVars;
		mAllGlobalPreVarsToProject = new HashSet<>();
		mAllGlobalPrimedToUnprimed = new HashMap<>();
		for (final IProgramVar pv : mSymbolTable.getAllGlobalBaseVars()) {
			mAllGlobalPreVarsToProject.add(pv.getTermVariable());
			final TermVariable primed = mSymbolTable.getPrimedVar(pv);
			if (primed != null) {
				mAllGlobalPrimedToUnprimed.put(primed, pv.getTermVariable());
			}
		}
	}

	public void setStats(final SifaStats stats) {
		mStats = stats;
	}

	public IPredicate strongestPostcondition(final IPredicate statePredicate, final IPredicate relationalPredicate) {
		return strongestPostcondition(statePredicate, prepareRelation(relationalPredicate));
	}

	public PreparedRelation prepareRelation(final IPredicate relationalPredicate) {
		if (mProjectAllGlobalPreVars) {
			return new PreparedRelation(relationalPredicate, mAllGlobalPreVarsToProject, mAllGlobalPrimedToUnprimed);
		}
		final Set<TermVariable> preVarsToProject = new HashSet<>();
		final Map<Term, Term> primedToUnprimed = new HashMap<>();
		for (final IProgramVar pv : relationalPredicate.getVars()) {
			if (mSymbolTable.isPrimedVar(pv)) {
				final IProgramVar baseVar = mSymbolTable.getBaseVar(pv);
				primedToUnprimed.put(pv.getTermVariable(), baseVar.getTermVariable());
				preVarsToProject.add(baseVar.getTermVariable());
			} else if (mSymbolTable.getPrimedVar(pv) != null) {
				preVarsToProject.add(pv.getTermVariable());
			}
		}
		return new PreparedRelation(relationalPredicate, preVarsToProject, primedToUnprimed);
	}

	public Set<TermVariable> primedVariablesIn(final IPredicate relationalPredicate) {
		if (mProjectAllGlobalPreVars) {
			return mAllGlobalPrimedToUnprimed.keySet().stream().map(TermVariable.class::cast)
					.collect(Collectors.toUnmodifiableSet());
		}
		final Set<TermVariable> primedVariables = new HashSet<>();
		for (final IProgramVar pv : relationalPredicate.getVars()) {
			if (mSymbolTable.isPrimedVar(pv)) {
				primedVariables.add(pv.getTermVariable());
			}
		}
		return Set.copyOf(primedVariables);
	}

	public IPredicate strongestPostcondition(final IPredicate statePredicate, final PreparedRelation preparedRelation) {
		if (SmtUtils.isFalseLiteral(statePredicate.getFormula())
				|| SmtUtils.isFalseLiteral(preparedRelation.relation().getFormula())) {
			return mPredicateFactory.newPredicate(mManagedScript.getScript().term("false"));
		}
		final Term conjunction = SmtUtils.and(mManagedScript.getScript(), statePredicate.getFormula(),
				preparedRelation.relation().getFormula());
		if (SmtUtils.isFalseLiteral(conjunction)) {
			return mPredicateFactory.newPredicate(conjunction);
		}

		final Set<TermVariable> preVarsToProject = preparedRelation.preVarsToProject();
		final Term projected;
		if (preVarsToProject.isEmpty() || !RelationalPredicateUtils.hasFreeVarIn(conjunction, preVarsToProject)) {
			projected = conjunction;
		} else {
			if (mStats != null) {
				mStats.increment(SifaStats.Key.INTERFERENCE_QE_APPLICATIONS);
				mStats.start(SifaStats.Key.INTERFERENCE_QE_TIME);
				mStats.startMax(SifaStats.Key.INTERFERENCE_QE_MAX_TIME);
			}
			projected = RelationalPredicateUtils.existentiallyProject(conjunction, preVarsToProject, mServices,
					mManagedScript);
			if (mStats != null) {
				mStats.stop(SifaStats.Key.INTERFERENCE_QE_TIME);
				mStats.stopMax(SifaStats.Key.INTERFERENCE_QE_MAX_TIME);
			}
		}

		final Map<Term, Term> primedToUnprimed = preparedRelation.primedToUnprimed();
		final Term renamed;
		if (primedToUnprimed.isEmpty() || !RelationalPredicateUtils.hasFreeVarIn(projected, primedToUnprimed.keySet())) {
			renamed = projected;
		} else {
			renamed = Substitution.apply(mManagedScript, primedToUnprimed, projected);
		}

		return mPredicateFactory.newPredicate(renamed);
	}

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public BasicPredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}

	public PrimedDefaultIcfgSymbolTable getSymbolTable() {
		return mSymbolTable;
	}
}
