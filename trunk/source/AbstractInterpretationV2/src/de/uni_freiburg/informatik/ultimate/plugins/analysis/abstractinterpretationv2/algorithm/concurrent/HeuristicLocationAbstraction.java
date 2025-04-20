package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

public class HeuristicLocationAbstraction<LOC extends IcfgLocation> {
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private final int locationCounter = 0;
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final IIcfg<? extends LOC> mIcfg;
	private final IUltimateServiceProvider mServices;
	private final Term mTrueTerm;
	private final Set<IProgramNonOldVar> mGlobals;

	public HeuristicLocationAbstraction(final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mScript = mManagedScript.getScript();
		mIcfg = icfg;
		mServices = services;
		mTrueTerm = mManagedScript.term(this, "false");
		mGlobals = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals();
	}

	public AbstractLocationMap<LOC> computeLocationAbstraction() {
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

	private boolean shouldDifferentiate(final List<IcfgEdge> outgoing) {
		if (outgoing.isEmpty()) {
			return false;
		}
		// forks, "assume true", ...
		if (isSkipStatement(outgoing)) {
			return false;
		}
		// (?) must be assert statement?
		if (outgoing.stream().anyMatch(s -> ((BoogieIcfgLocation) s.getTarget()).isErrorLocation())) {
			return false;
		}
		final boolean containsAssume = containsAssume(outgoing);
		final boolean edgeUnionTop = isEdgeUnionTop(outgoing);
		if (containsAssume
				&& ((!edgeUnionTop || outgoing.size() == 1) || (edgeUnionTop && assumeContainsGlobal(outgoing)))) {
			return true;
		}
		return false;
	}

	private boolean isSkipStatement(final List<IcfgEdge> outgoing) {
		return outgoing.stream().anyMatch(
				s -> s.getTransformula().getInVars().size() == 0 && s.getTransformula().getOutVars().size() == 0);
	}

	private boolean assumeContainsGlobal(final List<IcfgEdge> outgoing) {
		for (final IcfgEdge icfgEdge : outgoing) {
			final var invars = icfgEdge.getTransformula().getInVars();
			if (mGlobals.stream().anyMatch(invars.keySet()::contains)) {
				return true;
			}
		}
		return false;
	}

	private boolean containsAssume(final List<IcfgEdge> outgoing) {
		for (final IcfgEdge icfgEdge : outgoing) {
			if (!hasGuard(icfgEdge.getTransformula())) {
				return false;
			}
		}
		return true;
	}

	private boolean hasGuard(final UnmodifiableTransFormula tf) {
		final boolean hasAssignments = !tf.getAssignedVars().isEmpty();
		if (hasAssignments) {
			return false;
		}
//		final Term guard = TransFormulaUtils.computeGuardTerm(mServices, mManagedScript, tf, false);
//		final boolean hasGuard = termIsTrue(guard);
//
//		if (hasGuard) {
//			return true;
//		}
//		return false;
		return true;
	}

	private boolean isEdgeUnionTop(final List<IcfgEdge> outgoing) {
		final var terms = outgoing.stream().map(e -> e.getTransformula().getClosedFormula()).toList();
		final var union = SmtUtils.or(mScript, terms);
		return termIsTrue(union);
	}

	private boolean termIsTrue(final Term term) {
		mManagedScript.lock(this);
		mManagedScript.push(this, 1);
		mManagedScript.assertTerm(this, term);
		mManagedScript.assertTerm(this, SmtUtils.not(mScript, term));
		final LBool checkSatResult = mManagedScript.checkSat(this);
		mManagedScript.pop(this, 1);
		mManagedScript.unlock(this);
		if (checkSatResult.equals(LBool.UNSAT)) {
			return true;
		}
		return false;
	}

}
