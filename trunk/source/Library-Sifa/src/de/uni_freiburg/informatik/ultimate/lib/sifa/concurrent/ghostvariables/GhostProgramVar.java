package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * A ghost program variable, used for tracking analysis state like control locations or thread counters.
 */
public final class GhostProgramVar implements IProgramVar {

	private static final long serialVersionUID = 1L;

	private final String mName;
	private final TermVariable mTermVariable;
	private final ApplicationTerm mDefaultConstant;
	private final ApplicationTerm mPrimedConstant;

	private GhostProgramVar(final String name, final TermVariable termVariable, final ApplicationTerm defaultConstant,
			final ApplicationTerm primedConstant) {
		mName = name;
		mTermVariable = termVariable;
		mDefaultConstant = defaultConstant;
		mPrimedConstant = primedConstant;
	}

	public static GhostProgramVar construct(final String name, final Sort sort, final ManagedScript script,
			final Object lockOwner) {
		final TermVariable tv = script.constructFreshTermVariable(name, sort);
		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(script, lockOwner, sort, name);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(script, lockOwner, sort, name);
		return new GhostProgramVar(name, tv, defaultConstant, primedConstant);
	}

	@Override
	public String getGloballyUniqueId() {
		return mName;
	}

	@Override
	public boolean isGlobal() {
		return true;
	}

	@Override
	public boolean isOldvar() {
		return false;
	}

	@Override
	public TermVariable getTermVariable() {
		return mTermVariable;
	}

	@Override
	public String getProcedure() {
		return null;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		return mDefaultConstant;
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		return mPrimedConstant;
	}

	@Override
	public Term getTerm() {
		return mTermVariable;
	}

	@Override
	public String toString() {
		return mName;
	}
}
