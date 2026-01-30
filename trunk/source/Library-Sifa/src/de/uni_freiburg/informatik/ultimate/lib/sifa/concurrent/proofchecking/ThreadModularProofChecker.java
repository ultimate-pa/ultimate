package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Proof checking: (1) initial locations, (2) inductiveness, (3) interference freedom.
 */
public class ThreadModularProofChecker {

	private final ILogger mLogger;
	private final InductivenessCheck mInductivenessCheck;
	private final InterferenceFreedomCheck mInterferenceCheck;

	public ThreadModularProofChecker(final ILogger logger, final CfgSmtToolkit cfgSmtToolkit,
			final RelationalPredicatePostcondition postcondition, final IDomain domain) {
		mLogger = logger;
		mInductivenessCheck = new InductivenessCheck(new MonolithicHoareTripleChecker(cfgSmtToolkit));
		mInterferenceCheck = new InterferenceFreedomCheck(postcondition, domain);
	}

	public ProofCheckResult checkAll(final IIcfg<IcfgLocation> icfg,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IInterferenceAbstraction interferences,
			final Map<String, Map<IcfgLocation, IPredicate>> threadPredicates) {

		final List<String> allViolations = new ArrayList<>();

		final ProofCheckResult initialResult = InitialLocationCheck.check(icfg, locationPredicates);
		if (!initialResult.isValid()) {
			allViolations.addAll(initialResult.getViolations());
		}

		final ProofCheckResult inductiveResult = mInductivenessCheck.check(locationPredicates);
		if (!inductiveResult.isValid()) {
			allViolations.addAll(inductiveResult.getViolations());
		}

		final ProofCheckResult interferenceResult = mInterferenceCheck.checkAllThreads(threadPredicates, interferences);
		if (!interferenceResult.isValid()) {
			allViolations.addAll(interferenceResult.getViolations());
		}

		if (allViolations.isEmpty()) {
			mLogger.info("Proof check: PASSED");
			return ProofCheckResult.valid();
		}
		mLogger.warn("Proof check: FAILED (%d violations)", allViolations.size());
		return ProofCheckResult.invalid(allViolations);
	}

	public ProofCheckResult checkAll(final IIcfg<IcfgLocation> icfg,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IInterferenceAbstraction interferences) {
		final Map<String, Map<IcfgLocation, IPredicate>> threadPredicates = new HashMap<>();
		for (final Map.Entry<IcfgLocation, IPredicate> entry : locationPredicates.entrySet()) {
			final String procedure = entry.getKey().getProcedure();
			threadPredicates.computeIfAbsent(procedure, k -> new HashMap<>()).put(entry.getKey(), entry.getValue());
		}
		return checkAll(icfg, locationPredicates, interferences, threadPredicates);
	}
}
