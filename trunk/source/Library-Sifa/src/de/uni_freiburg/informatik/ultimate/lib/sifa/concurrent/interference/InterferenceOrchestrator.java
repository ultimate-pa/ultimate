package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.InterferenceCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.InterferenceCollector.ThreadAnalysisInput;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint.BasicFixpointStrategy;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint.IInterferenceFixpointStrategy;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.transformers.IInterferenceTransformer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

/**
 * Orchestrates interference collection, transformation, merging, and
 * application.
 */
public class InterferenceOrchestrator {

    private final ILogger mLogger;

    private final IDomain mDomain;
    private final RelationalPredicatePostcondition mPostcondition;
    private final IInterferenceFixpointStrategy mFixpointStrategy;
    private final InterferenceCollector mCollector;
    private final IInterferenceTransformer mTransformer;
    private final IInterferenceMerger mMerger;
    private InterferenceAbstraction mInterferences;

    public InterferenceOrchestrator(final IDomain domain, final RelationalPredicatePostcondition postcondition,
            final InterferenceCollector collector, final ILogger logger) {
        this(domain, postcondition, collector, IInterferenceTransformer.identity(), IInterferenceMerger.identity(),
                new BasicFixpointStrategy(), logger);
    }

    public InterferenceOrchestrator(final IDomain domain, final RelationalPredicatePostcondition postcondition,
            final InterferenceCollector collector, final IInterferenceTransformer transformer,
            final IInterferenceMerger merger, final ILogger logger) {
        this(domain, postcondition, collector, transformer, merger, new BasicFixpointStrategy(), logger);
    }

    public InterferenceOrchestrator(final IDomain domain, final RelationalPredicatePostcondition postcondition,
            final InterferenceCollector collector, final IInterferenceTransformer transformer,
            final IInterferenceMerger merger, final IInterferenceFixpointStrategy fixpointStrategy,
            final ILogger logger) {
        mDomain = domain;
        mPostcondition = postcondition;
        mCollector = collector;
        mTransformer = transformer;
        mMerger = merger;
        mFixpointStrategy = fixpointStrategy;
        mInterferences = InterferenceAbstraction.empty();
        mLogger = logger;
    }

    public void updateInterferences(final Map<String, ThreadAnalysisInput> analysisResults) {
        InterferenceAbstraction interferences = mCollector.collectFromAllThreads(analysisResults);
        // Debug: log collected interferences
        logItfs(interferences);
        interferences = mTransformer.transform(interferences);
        interferences = mMerger.merge(interferences, mDomain);
        mInterferences = interferences;
    }

    private void logItfs(final InterferenceAbstraction interferences) {
        mLogger.info("=== Collected Interferences ===");
        for (final String threadId : interferences.getThreadIds()) {
            final Set<IPredicate> threadItfs = interferences.getInterferencesProducedBy(threadId);
            mLogger.info("Thread %s produced %d interferences:", threadId, threadItfs.size());
            for (final IPredicate itf : threadItfs) {
                mLogger.info("  - %s", itf.getFormula());
            }
        }
        mLogger.info("================================");
    }

    public InterferenceAbstraction getInterferences() {
        return mInterferences;
    }

    public Set<IPredicate> getInterferencesFor(final String threadId) {
        if (mInterferences != null) {
            return mInterferences.getInterferencesForOtherThreads(threadId);
        }
        final Set<IPredicate> result = new HashSet<>();
        for (final String otherId : mInterferences.getThreadIds()) {
            if (!otherId.equals(threadId)) {
                result.addAll(mInterferences.getInterferencesProducedBy(otherId));
            }
        }
        return result;
    }

    public IPredicate itfFixpoint(final IPredicate state, final String threadId) {
        final Set<IPredicate> interferences = getInterferencesFor(threadId);
        if (interferences.isEmpty()) {
            mLogger.info("itfFixpoint(%s): no interferences, state unchanged", threadId);
            return state;
        }
        mLogger.info("itfFixpoint(%s): applying %d interferences to state: %s",
                threadId, interferences.size(), state.getFormula());
        final IPredicate result = mFixpointStrategy.computeFixpoint(state, interferences, mDomain, mPostcondition);
        mLogger.info("itfFixpoint(%s): result: %s", threadId, result.getFormula());
        return result;
    }
}
