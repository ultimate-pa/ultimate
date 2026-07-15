package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PrimedDefaultIcfgSymbolTable extends DefaultIcfgSymbolTable {

	private final ManagedScript mManagedScript;
	private final Map<IProgramVar, TermVariable> mPrimedVars = new HashMap<>();
	private final Set<IProgramVar> mGhostVars = new HashSet<>();
	private Set<IProgramVar> mCachedGlobalBaseVars;

	public PrimedDefaultIcfgSymbolTable(final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ManagedScript managedScript) {
		super(symbolTable, procedures);
		mManagedScript = managedScript;
		addPrimedMappings(procedures, managedScript);
		finishConstruction();
	}

	public void registerGhostVariable(final IProgramVar ghostVar) {
		mCachedGlobalBaseVars = null;
		mGhostVars.add(ghostVar);
		mTermVariable2ProgramVar.put(ghostVar.getTermVariable(), ghostVar);

		final TermVariable primedTv = mManagedScript.constructFreshTermVariable(
				ghostVar.getGloballyUniqueId() + "_primed", ghostVar.getTermVariable().getSort());
		mTermVariable2ProgramVar.put(primedTv, new PrimedProgramVar(ghostVar, primedTv));
		mPrimedVars.put(ghostVar, primedTv);

		addDefaultConstant(ghostVar);
		addPrimedConstant(ghostVar);
	}

	@Override
	public Set<ApplicationTerm> computeAllDefaultConstants() {
		final Set<ApplicationTerm> rtr = new LinkedHashSet<>(super.computeAllDefaultConstants());
		mGhostVars.stream().map(IProgramVar::getDefaultConstant).forEachOrdered(rtr::add);
		return rtr;
	}

	public Set<IProgramVar> getAllGlobalBaseVars() {
		if (mCachedGlobalBaseVars != null) {
			return mCachedGlobalBaseVars;
		}
		final Set<IProgramVar> result = new HashSet<>();
		for (final IProgramVar pv : mTermVariable2ProgramVar.values()) {
			if (!pv.isGlobal() || pv.isOldvar() || isPrimedVar(pv)) {
				continue;
			}
			result.add(pv);
		}
		mCachedGlobalBaseVars = result;
		return mCachedGlobalBaseVars;
	}

	public TermVariable getPrimedVar(final IProgramVar var) {
		return mPrimedVars.get(var);
	}

	public boolean isPrimedVar(final IProgramVar var) {
		return var instanceof PrimedProgramVar;
	}

	public IProgramVar getBaseVar(final IProgramVar var) {
		if (var instanceof PrimedProgramVar) {
			return ((PrimedProgramVar) var).mBase;
		}
		return var;
	}

	private void addPrimedMappings(final Set<String> procedures, final ManagedScript managedScript) {
		final Set<IProgramVar> vars = new HashSet<>();
		vars.addAll(getGlobals());
		for (final String procedure : procedures) {
			vars.addAll(getLocals(procedure));
		}

		for (final IProgramVar var : vars) {
			final TermVariable primedVar = managedScript
					.constructFreshTermVariable(var.getGloballyUniqueId() + "_primed", var.getTermVariable().getSort());
			mTermVariable2ProgramVar.put(primedVar, new PrimedProgramVar(var, primedVar));
			mPrimedVars.put(var, primedVar);
			addDefaultConstant(var);
			addPrimedConstant(var);
		}
	}

	private void addDefaultConstant(final IProgramVar var) {
		final ApplicationTerm defaultConstant = var.getDefaultConstant();
		final FunctionSymbol funSym = defaultConstant.getFunction();
		if (mFunSym2ProgramFunction.containsKey(funSym)) {
			return;
		}
		final IProgramConst defaultConst = new ProgramConst(var.getGloballyUniqueId(), defaultConstant, false);
		mFunSym2ProgramFunction.put(funSym, defaultConst);
		mConstants.add(defaultConst);
	}

	private void addPrimedConstant(final IProgramVar var) {
		final ApplicationTerm primedConstant = var.getPrimedConstant();
		final FunctionSymbol funSym = primedConstant.getFunction();
		if (mFunSym2ProgramFunction.containsKey(funSym)) {
			return;
		}
		final IProgramConst primedConst = new ProgramConst(var.getGloballyUniqueId() + "_primed", primedConstant,
				false);
		mFunSym2ProgramFunction.put(funSym, primedConst);
		mConstants.add(primedConst);
	}

	private static final class PrimedProgramVar implements IProgramVar {
		private static final long serialVersionUID = 1L;
		private final IProgramVar mBase;
		private final TermVariable mPrimedTermVariable;

		private PrimedProgramVar(final IProgramVar base, final TermVariable primedTermVariable) {
			mBase = base;
			mPrimedTermVariable = primedTermVariable;
		}

		@Override
		public String getGloballyUniqueId() {
			return mBase.getGloballyUniqueId() + "_primed";
		}

		@Override
		public boolean isGlobal() {
			return mBase.isGlobal();
		}

		@Override
		public boolean isOldvar() {
			return false;
		}

		@Override
		public TermVariable getTermVariable() {
			return mPrimedTermVariable;
		}

		@Override
		public String getProcedure() {
			return mBase.getProcedure();
		}

		@Override
		public ApplicationTerm getPrimedConstant() {
			return mBase.getPrimedConstant();
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			return mBase.getPrimedConstant();
		}

		@Override
		public Term getTerm() {
			return mPrimedTermVariable;
		}

		@Override
		public String toString() {
			return mBase.toString() + "'";
		}
	}
}
