package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;

public class HeuristicLocationAbstraction<LOC extends IcfgLocation> {
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final IIcfg<? extends LOC> mIcfg;
	private final Set<IProgramNonOldVar> mGlobals;
	private final IUltimateServiceProvider mServices;
	private boolean mMutexReached;
	private String mLastThreadString;

	public HeuristicLocationAbstraction(final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mScript = mManagedScript.getScript();
		mIcfg = icfg;
		mGlobals = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
		mServices = services;
		mMutexReached = false;
	}

	public AbstractLocationMap<LOC> computeLocationAbstraction() {
		mMutexReached = false;
		mLastThreadString = "Ultimate.start";
		final AbstractLocationMap<LOC> x = new AbstractLocationMap<>(l -> {
			if (!l.getProcedure().equals(mLastThreadString)) {
				mLastThreadString = l.getProcedure();
				mMutexReached = false;
			}
			final var outgoing = l.getOutgoingEdges();
			final String sourceThread = l.getProcedure();
			if (shouldDifferentiate(outgoing) && !mMutexReached) {
				mMutexReached = true;
				return getAndIncrementThreadLocationCounter(sourceThread);
			} else if (!mMutexReached) {
				return getAndIncrementThreadLocationCounter(sourceThread);
			}
			return getThreadLocationCounter(sourceThread);
		}, mIcfg.getProcedureEntryNodes());
		return x;
	}

	public AbstractLocationMap<LOC> computeMine() {
		final AbstractLocationMap<LOC> x = new AbstractLocationMap<>(l -> {
			final var outgoing = l.getOutgoingEdges();
			final String sourceThread = l.getProcedure();
			if (shouldDifferentiate(outgoing)) {
				return getAndIncrementThreadLocationCounter(sourceThread);
			}
			return getThreadLocationCounter(sourceThread);
		}, mIcfg.getProcedureEntryNodes());
		return x;
	}

	private int getThreadLocationCounter(final String thread) {
		return mPerThreadLocationCounterMap.getOrDefault(thread, 0);
	}

	private int getAndIncrementThreadLocationCounter(final String thread) {
		final int counter = mPerThreadLocationCounterMap.getOrDefault(thread, 0);
		mPerThreadLocationCounterMap.put(thread, counter + 1);
		return counter;
	}

	public boolean shouldDifferentiate(final List<IcfgEdge> outgoing) {
		final var guards = outgoing.stream()
				.map(e -> TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, e.getTransformula(), false))
				.toList();
		final var term = SmtUtils.simplify(mManagedScript, SmtUtils.or(mScript, guards), mServices,
				SimplificationTechnique.POLY_PAC);
		final var globals = mGlobals.stream().map(v -> v.getTermVariable()).collect(Collectors.toSet());
		return Arrays.stream(term.getFreeVars()).anyMatch(globals::contains);
	}
}
