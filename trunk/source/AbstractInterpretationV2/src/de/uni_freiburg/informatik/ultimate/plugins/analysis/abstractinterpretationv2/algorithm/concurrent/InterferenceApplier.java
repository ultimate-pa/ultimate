package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
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

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToDisjState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferingState,
			final ACTION action,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> targetState,
			final IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> postOp,
			final int maxSize, final boolean isSelfInterfering, final IIcfg<?> cfg) {

		if (targetState.isBottom() || interferingState.isBottom()) {
			return null;
		}
		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> globalTargetState = targetState;
		final Map<IProgramVarOrConst, IProgramVarOrConst> reverseRenamedMap = new HashMap<>();
		if (isSelfInterfering) {
			if (!cfg.getCfgSmtToolkit().getManagedScript().isLocked()) {
				cfg.getCfgSmtToolkit().getManagedScript().lock(this);
			}
			final Collection<ILocalProgramVar> locals1 = cfg.getCfgSmtToolkit().getSymbolTable()
					.getLocals(action.getPrecedingProcedure());
			final Collection<IProgramVarOrConst> locals = new HashSet<>(locals1);
			for (final IProgramVarOrConst v : locals) {
				final var newVar = ProgramVarUtils.constructLocalProgramVar(v.getGloballyUniqueId() + UNIQUEINT++ + "'",
						action.getPrecedingProcedure(), v.getSort(), cfg.getCfgSmtToolkit().getManagedScript(), this);
				reverseRenamedMap.put(newVar, v);
				globalTargetState = globalTargetState.renameVariable(v, newVar);
			}
		} else {
			globalTargetState = targetState;
		}
		// Add local variables to both states to be able to intersect
		final var adjustedTarget = adjustStateForIntersection(globalTargetState, interferingState, maxSize);
		final var adjustedInterferer = adjustStateForIntersection(interferingState, globalTargetState, maxSize);

		final var intersectionState = adjustedTarget.intersect(adjustedInterferer);

		// throw out false states from intersection
		final var filtered = filterStates(intersectionState, maxSize);
		if (filtered.getStates().size() == 0 || filtered.isBottom()) {
			if (cfg.getCfgSmtToolkit().getManagedScript().isLocked()) {
				cfg.getCfgSmtToolkit().getManagedScript().unlock(this);
			}
			return null;
		}
		// postop
		var postState = filtered.apply(postOp, action);
		GuardedInterferenceDomain.postoperatorCalls++;

		// TODO: sound?
		if (postState.isEmpty() || postState.isBottom()) {
			if (cfg.getCfgSmtToolkit().getManagedScript().isLocked()) {
				cfg.getCfgSmtToolkit().getManagedScript().unlock(this);
			}
			return null;
		}
		// remove local variables of other state we added earlier
		final var missingLocals = DataStructureUtils.difference(interferingState.getVariables(),
				globalTargetState.getVariables());
		if (!missingLocals.isEmpty()) {
			postState = postState.removeVariables(missingLocals);
		}
		if (isSelfInterfering) {
			for (final IProgramVarOrConst tempVar : reverseRenamedMap.keySet()) {
				postState = postState.renameVariable(tempVar, reverseRenamedMap.get(tempVar));
			}
			if (cfg.getCfgSmtToolkit().getManagedScript().isLocked()) {
				cfg.getCfgSmtToolkit().getManagedScript().unlock(this);
			}
		}
		return postState;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustStateForIntersection(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustee,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> target,
			final int maxSize) {
		final var missingLocals = DataStructureUtils.difference(target.getVariables(), adjustee.getVariables());
		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjusteeWithForeignLocals;
		if (!missingLocals.isEmpty()) {
			adjusteeWithForeignLocals = adjustee.addVariables(missingLocals);
		} else {
			adjusteeWithForeignLocals = adjustee;
		}
		final var filteredState = filterStates(adjusteeWithForeignLocals, maxSize);
		return filteredState;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> filterStates(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> filterMe,
			final int maxSize) {
		return DisjunctiveAbstractState.createDisjunction(filterMe.getStates().stream().filter(
				s -> s != null && !s.isBottom() && s.threadCounter() != null && s.abstractLocationState() != null)
				.collect(Collectors.toSet()), maxSize);
	}

}
