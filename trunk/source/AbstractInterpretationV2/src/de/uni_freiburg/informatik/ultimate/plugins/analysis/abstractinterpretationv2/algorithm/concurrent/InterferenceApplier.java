package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private static int UNIQUEINT = 0;
	private final InterferenceCache<STATE, ACTION, LOC> mCache;

	public InterferenceApplier(final InterferenceCache<STATE, ACTION, LOC> cache) {
		mCache = cache;
	}

	public Collection<InterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToStateNonRelational(
			final InterferenceDomainState<STATE, ACTION, LOC> interferingStateGuarded, final ACTION action,
			final InterferenceDomainState<STATE, ACTION, LOC> targetStateGuarded,
			final InterferenceDomainPostOperator<STATE, ACTION, LOC> postOp, final boolean isSelfInterfering,
			final IIcfg<?> cfg) {

		final var threadCounterPost = postOp.applyThreadCounter(targetStateGuarded.threadCounter(),
				targetStateGuarded.abstractLocationState(), action);
		final boolean isinfinite = targetStateGuarded.threadCounter().getThreadInstances()
				.get(action.getPrecedingProcedure()).getUpper().isInfinity();
		final var absLocPost = postOp.applyAbstractLocation(targetStateGuarded.abstractLocationState(), action,
				isSelfInterfering, isinfinite);
		final var touple = new StateItfPair<>(targetStateGuarded.state(), action);
		final var cached = mCache.getSimpleItfCache().get(touple);
		if (cached != null) {
			InterferenceDomain.applierCacheHits++;
			return cached.stream()
					.map(s -> new InterferenceDomainState<STATE, ACTION, LOC>(s, threadCounterPost, absLocPost))
					.toList();
		}
		/*
		 * Add local variables to both states to be able to intersect. This is necessary since our interference
		 * transition might contain local variables of the interfering thread.
		 */
		final var adjustedTarget = adjustStateForIntersection(targetStateGuarded.state(),
				interferingStateGuarded.state());
		// postop
		var postState = postOp.applyState(adjustedTarget, action).stream().filter(s -> !s.isBottom()).toList();
		InterferenceDomain.postoperatorCalls++;

		// remove local variables of other state we added earlier
		final var missingLocals = DataStructureUtils.difference(interferingStateGuarded.getVariables(),
				targetStateGuarded.getVariables());
		if (!missingLocals.isEmpty()) {
			postState = postState.stream().map(s -> s.removeVariables(missingLocals)).toList();
		}
		final var postStateWithGuard = postState.stream()
				.map(s -> new InterferenceDomainState<STATE, ACTION, LOC>(s, threadCounterPost, absLocPost)).toList();

		mCache.getSimpleItfCache().put(touple, postState);
		return postStateWithGuard;
	}

	public Collection<InterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToState(
			final InterferenceDomainState<STATE, ACTION, LOC> interferingStateGuarded, final ACTION action,
			final InterferenceDomainState<STATE, ACTION, LOC> targetStateGuarded,
			final InterferenceDomainPostOperator<STATE, ACTION, LOC> postOp, final boolean isSelfInterfering,
			final IIcfg<?> cfg) {

		if (targetStateGuarded.isBottom() || interferingStateGuarded.isBottom()) {
			return Collections.emptyList();
		}
		final var intervalCounterValue = interferingStateGuarded.threadCounter().getThreadInstances()
				.get(action.getPrecedingProcedure());
		if (intervalCounterValue.isBottom()) {
			return Collections.emptyList();
		}

		final var threadCounterIntersection = targetStateGuarded.threadCounter()
				.intersect(interferingStateGuarded.threadCounter());
		AbstractLocationState<LOC> abslocIntersection;
		if (isSelfInterfering) {
			// TODO
			abslocIntersection = targetStateGuarded.abstractLocationState()
					.intersectSelf(interferingStateGuarded.abstractLocationState());
		} else {
			abslocIntersection = targetStateGuarded.abstractLocationState()
					.intersect(interferingStateGuarded.abstractLocationState());
		}

		// TODO: cleanup
		if (threadCounterIntersection == null || threadCounterIntersection.getThreadInstances().values().stream()
				.anyMatch(c -> c == null || c.isBottom()) || abslocIntersection == null) {
			return Collections.emptyList();
		}

		final var threadCounterPost = postOp.applyThreadCounter(threadCounterIntersection, abslocIntersection, action);

		final boolean isinfinite = targetStateGuarded.threadCounter().getThreadInstances()
				.get(action.getPrecedingProcedure()).getUpper().isInfinity();
		final var absLocPost = postOp.applyAbstractLocation(abslocIntersection, action, isSelfInterfering, isinfinite);

		if (threadCounterPost == null || absLocPost == null) {
			return Collections.emptyList();
		}

		final var targetState = targetStateGuarded.state();
		final var interferingState = interferingStateGuarded.state();
		final var triple = new StateItfPrestatePair<>(targetState, interferingState, action);
		final var cached = mCache.getItfCache().get(triple);
		if (cached != null) {
			InterferenceDomain.applierCacheHits++;
			return cached.stream()
					.map(s -> new InterferenceDomainState<STATE, ACTION, LOC>(s, threadCounterPost, absLocPost))
					.toList();
		}

		STATE globalTargetState = targetState;
		final Map<IProgramVarOrConst, IProgramVarOrConst> reverseRenamedMap = new HashMap<>();
		/*
		 * In the case of an interference interfering in a state of its own ownerThread, our local program variables
		 * clash, and cannot be distinguished, but are variables of different threads with potentially different values.
		 * The interference computation needs the local vars of the prestate of the interference, since the transition
		 * might contain a local variable of that prestate, and we need the value of that var as it was during the
		 * creation of the interference.
		 *
		 * This is why we have to rename the local vars of the interfered state while computing the interference
		 * application, so they dont clash or get lost, and later rename them back, and toss away the prestate local
		 * vars.
		 */
		if (isSelfInterfering) {
			cfg.getCfgSmtToolkit().getManagedScript().lock(this);
			final Collection<ILocalProgramVar> locals1 = cfg.getCfgSmtToolkit().getSymbolTable()
					.getLocals(action.getPrecedingProcedure());
			final Collection<IProgramVarOrConst> locals = new HashSet<>(locals1);
			for (final IProgramVarOrConst v : locals) {
				final var newVar = ProgramVarUtils.constructLocalProgramVar(
						v.getGloballyUniqueId() + "_itfCopy" + UNIQUEINT++, action.getPrecedingProcedure(), v.getSort(),
						cfg.getCfgSmtToolkit().getManagedScript(), this);
				reverseRenamedMap.put(newVar, v);
				globalTargetState = globalTargetState.renameVariable(v, newVar);
			}
			cfg.getCfgSmtToolkit().getManagedScript().unlock(this);
		} else {
			globalTargetState = targetState;
		}
		/*
		 * Add local variables to both states to be able to intersect. This is necessary since our interference
		 * transition might contain local variables of the interfering thread.
		 */
		final var adjustedTarget = adjustStateForIntersection(globalTargetState, interferingState);
		final var adjustedInterferer = adjustStateForIntersection(interferingState, globalTargetState);

		final var intersectionState = adjustedTarget.intersect(adjustedInterferer);

		// Throw out false states from intersection
		if (intersectionState == null || intersectionState.isBottom()) {
			mCache.getItfCache().put(triple, Collections.emptyList());
			return Collections.emptyList();
		}
		// postop
		var postState = postOp.applyState(intersectionState, action).stream().filter(s -> !s.isBottom()).toList();
		InterferenceDomain.postoperatorCalls++;

		// TODO: sound?
		if (postState.isEmpty()) {
			mCache.getItfCache().put(triple, Collections.emptyList());
			return Collections.emptyList();
		}
		// remove local variables of other state we added earlier
		final var missingLocals = DataStructureUtils.difference(interferingState.getVariables(),
				globalTargetState.getVariables());
		if (!missingLocals.isEmpty()) {
			postState = postState.stream().map(s -> s.removeVariables(missingLocals)).toList();
		}
		/*
		 * Rename our old local program variables, to get the real state of our local variables back. (which cannot
		 * change based on an interference, local vars are not accessible).
		 */
		if (isSelfInterfering) {
			for (final IProgramVarOrConst tempVar : reverseRenamedMap.keySet()) {
				postState = postState.stream().map(s -> s.renameVariable(tempVar, reverseRenamedMap.get(tempVar)))
						.toList();
			}
		}
		final var postStateWithGuard = postState.stream()
				.map(s -> new InterferenceDomainState<STATE, ACTION, LOC>(s, threadCounterPost, absLocPost)).toList();

		mCache.getItfCache().put(triple, postState);
		return postStateWithGuard;
	}

	private STATE adjustStateForIntersection(final STATE adjustee, final STATE target) {
		final var missingLocals = DataStructureUtils.difference(target.getVariables(), adjustee.getVariables());
		STATE adjusteeWithForeignLocals;
		if (!missingLocals.isEmpty()) {
			adjusteeWithForeignLocals = adjustee.addVariables(missingLocals);
		} else {
			adjusteeWithForeignLocals = adjustee;
		}
		return adjusteeWithForeignLocals;
	}
}
