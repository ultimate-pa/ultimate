package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PrimedTermvariableHelper {
	private final Map<IProgramVar, TermVariable> mPrimedVarMap;
	private final Map<TermVariable, TermVariable> mToNonPrimeVarMap;
	private final ManagedScript mScript;
	private final IIcfgSymbolTable mSymbolTable;

	public PrimedTermvariableHelper(final IIcfg<?> cfg) {
		new HashMap<>();
		mPrimedVarMap = new HashMap<>();
		mToNonPrimeVarMap = new HashMap<>();
		mScript = cfg.getCfgSmtToolkit().getManagedScript();
		mSymbolTable = cfg.getCfgSmtToolkit().getSymbolTable();
	}

	public TermVariable getNonPrimedVar(final IProgramVar var) {
		return var.getTermVariable();
	}

	public TermVariable getOrConstructPrimedVar(final IProgramVar var) {
		if (mPrimedVarMap.get(var) != null) {
			return mPrimedVarMap.get(var);
		}
		final var newVar = mScript.constructFreshTermVariable(var.getTermVariable().getName() + "'",
				var.getTermVariable().getSort());
		mPrimedVarMap.put(var, newVar);
		mToNonPrimeVarMap.put(newVar, getNonPrimedVar(var));
		return newVar;
	}

	public TermVariable getOrConstructPrimedVar(final TermVariable tv) {
		final IProgramVar var = getProgramVar(tv);
		return getOrConstructPrimedVar(var);
	}

	public TermVariable getUnPrimed(final TermVariable tv) {
		if (mToNonPrimeVarMap.get(tv) == null) {
			throw new IllegalArgumentException("Termvariable does not have unprimed version");
		}
		return mToNonPrimeVarMap.get(tv);
	}

	public IProgramVar getProgramVar(final TermVariable tv) {
		return mSymbolTable.getProgramVar(tv);
	}

	public Set<IProgramVarOrConst> getGlobals() {
		final Set<IProgramVarOrConst> globalSet = new HashSet<>();
		globalSet.addAll(mSymbolTable.getGlobals());
		return globalSet;
	}
}
