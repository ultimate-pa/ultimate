package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PrimedDefaultIcfgSymbolTable extends DefaultIcfgSymbolTable {

	private final Map<IProgramVar, TermVariable> mPrimedVars = new HashMap<>();

	public PrimedDefaultIcfgSymbolTable(final IIcfgSymbolTable symbolTable, final Set<String> procedures,
			final ManagedScript managedScript) {
		super(symbolTable, procedures);
		addPrimedMappings(procedures, managedScript);
		finishConstruction();
	}

	public Map<IProgramVar, TermVariable> getPrimedVars() {
		return Collections.unmodifiableMap(mPrimedVars);
	}

	/**
	 * Returns the primed term variable for the given program variable, or null if not found.
	 */
	public TermVariable getPrimedVar(final IProgramVar var) {
		return mPrimedVars.get(var);
	}

	/**
	 * Checks if the given program variable is a primed variable (created by this symbol table).
	 */
	public boolean isPrimedVar(final IProgramVar var) {
		return var instanceof PrimedProgramVar;
	}

	/**
	 * If the given variable is a primed variable, returns the underlying base variable. Otherwise returns the variable
	 * itself.
	 */
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
			for (final ILocalProgramVar local : getLocals(procedure)) {
				vars.add(local);
			}
		}

		for (final IProgramVar var : vars) {
			final TermVariable primedVar = managedScript.constructFreshTermVariable(
					var.getGloballyUniqueId() + "_primed", var.getTermVariable().getSort());
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
		final IProgramConst primedConst = new ProgramConst(var.getGloballyUniqueId() + "_primed", primedConstant, false);
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
