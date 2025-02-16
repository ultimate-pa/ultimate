package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;

public class PrimedTermvariableHelper {
	private final Map<IProgramVar, TermVariable> mPrimedVarMap;
	private final Map<IProgramVar, TermVariable> mDoublePrimedVarMap;
	private final Map<TermVariable, TermVariable> mToNonPrimeVarMap;
	private final ManagedScript mScript;
	private final IIcfgSymbolTable mSymbolTable;

	private final ILogger mLogger;

	public PrimedTermvariableHelper(final IIcfg<?> cfg, final IUltimateServiceProvider serviceProvider) {
		mLogger = serviceProvider.getLoggingService().getLogger(Activator.PLUGIN_ID);
		new HashMap<>();
		mPrimedVarMap = new HashMap<>();
		mDoublePrimedVarMap = new HashMap<>();
		mToNonPrimeVarMap = new HashMap<>();
		mScript = cfg.getCfgSmtToolkit().getManagedScript();
		mSymbolTable = cfg.getCfgSmtToolkit().getSymbolTable();
	}

	public TermVariable getOrConstructNonPrimedVar(final IProgramVar var) {
		// if (mNonPrimedVarMap.get(var) != null) {
		// return mNonPrimedVarMap.get(var);
		// }
		// final var newVar =
		// mScript.constructFreshTermVariable(var.getTermVariable().getName(), var.getTermVariable().getSort());
		// mLogger.error("creating " + newVar + "instead of " + var.getTermVariable());
		// mNonPrimedVarMap.put(var, newVar);
		// return newVar;
		return var.getTermVariable();
	}

	public TermVariable getOrConstructPrimedVar(final IProgramVar var) {
		if (mPrimedVarMap.get(var) != null) {
			return mPrimedVarMap.get(var);
		}
		final var newVar = mScript.variable(var.getTermVariable().getName() + "'", var.getTermVariable().getSort());
		mPrimedVarMap.put(var, newVar);
		mToNonPrimeVarMap.put(newVar, getOrConstructNonPrimedVar(var));
		return newVar;
	}

	public TermVariable getOrConstructPrimedVar(final TermVariable tv) {
		final IProgramVar var = getProgramVar(tv);
		return getOrConstructPrimedVar(var);
	}

	public TermVariable getOrConstructDoublePrimedVar(final IProgramVar var) {
		if (mDoublePrimedVarMap.get(var) != null) {
			return mDoublePrimedVarMap.get(var);
		}
		final var newVar = mScript.variable(var.getTermVariable().getName() + "''", var.getTermVariable().getSort());
		mDoublePrimedVarMap.put(var, newVar);
		mToNonPrimeVarMap.put(newVar, getOrConstructNonPrimedVar(var));
		return newVar;
	}

	public TermVariable getOrConstructDoublePrimedVar(final TermVariable tv) {
		final IProgramVar var = getProgramVar(tv);
		return getOrConstructDoublePrimedVar(var);
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
}
