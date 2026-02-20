package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.QuantifierEliminationMode;
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
	private final QuantifierEliminationMode mEliminationMode;
	private final Set<TermVariable> mAllGlobalPreVarsToProject;
	private final Map<Term, Term> mAllGlobalPrimedToUnprimed;

	public RelationalPredicatePostcondition(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable) {
		this(services, managedScript, predicateFactory, symbolTable, false, QuantifierEliminationMode.LIGHT);
	}

	public RelationalPredicatePostcondition(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable,
			final boolean projectAllGlobalPreVars) {
		this(services, managedScript, predicateFactory, symbolTable, projectAllGlobalPreVars,
				QuantifierEliminationMode.LIGHT);
	}

	public RelationalPredicatePostcondition(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final PrimedDefaultIcfgSymbolTable symbolTable,
			final boolean projectAllGlobalPreVars, final QuantifierEliminationMode eliminationMode) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mSymbolTable = symbolTable;
		mProjectAllGlobalPreVars = projectAllGlobalPreVars;
		mEliminationMode = eliminationMode;
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

	public IPredicate strongestPostcondition(final IPredicate statePredicate, final PreparedRelation preparedRelation) {
		final Term conjunction = SmtUtils.and(mManagedScript.getScript(), statePredicate.getFormula(),
				preparedRelation.relation().getFormula());

		final Term projected = RelationalPredicateUtils.existentiallyProject(conjunction,
				preparedRelation.preVarsToProject(), mServices, mManagedScript, mEliminationMode);

		final Term renamed = preparedRelation.primedToUnprimed().isEmpty() ? projected
				: Substitution.apply(mManagedScript, preparedRelation.primedToUnprimed(), projected);

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
