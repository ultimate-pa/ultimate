package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

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
			return Set.copyOf(mAllGlobalPrimedToUnprimed.keySet().stream().map(TermVariable.class::cast)
					.collect(Collectors.toSet()));
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
		if (preVarsToProject.isEmpty() || !hasFreeVarIn(conjunction, preVarsToProject)) {
			projected = conjunction;
		} else {
			if (mStats != null) {
				mStats.increment(SifaStats.Key.INTERFERENCE_QE_APPLICATIONS);
				mStats.start(SifaStats.Key.INTERFERENCE_QE_TIME);
				mStats.startMax(SifaStats.Key.INTERFERENCE_QE_MAX_TIME);
			}
			projected = RelationalPredicateUtils.existentiallyProject(conjunction, preVarsToProject, mServices,
					mManagedScript, mStats);
			if (mStats != null) {
				mStats.stop(SifaStats.Key.INTERFERENCE_QE_TIME);
				mStats.stopMax(SifaStats.Key.INTERFERENCE_QE_MAX_TIME);
			}
		}

		final Map<Term, Term> primedToUnprimed = preparedRelation.primedToUnprimed();
		final Term renamed;
		if (primedToUnprimed.isEmpty() || !hasFreeVarIn(projected, primedToUnprimed.keySet())) {
			renamed = projected;
		} else {
			renamed = Substitution.apply(mManagedScript, primedToUnprimed, projected);
		}

		return mPredicateFactory.newPredicate(renamed);
	}

	private static boolean hasFreeVarIn(final Term term, final Set<? extends Term> candidates) {
		for (final TermVariable freeVar : term.getFreeVars()) {
			if (candidates.contains(freeVar)) {
				return true;
			}
		}
		return false;
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
