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
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {

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
			final Collection<ILocalProgramVar> locals = cfg.getCfgSmtToolkit().getSymbolTable()
					.getLocals(action.getPrecedingProcedure());
			final Collection<IProgramVarOrConst> progVarLocals = new HashSet<>(locals);
			for (final IProgramVarOrConst v : progVarLocals) {
				final var newVar = new LocalProgramVarDummy();
				reverseRenamedMap.put(newVar, v);
				globalTargetState = globalTargetState.renameVariable(v, newVar);
			}
		} else {
			globalTargetState = targetState;
		}

		/*
		 * Add local variables to both states to be able to intersect. This is necessary since our interference
		 * transition might contain local variables of the interfering thread.
		 */
		final var adjustedTarget = adjustStateForIntersection(globalTargetState, interferingState, maxSize);
		final var adjustedInterferer = adjustStateForIntersection(interferingState, globalTargetState, maxSize);

		final var intersectionState = adjustedTarget.intersect(adjustedInterferer);

		// Throw out false states from intersection
		final var filtered = filterStates(intersectionState, maxSize);
		if (filtered.getStates().isEmpty() || filtered.isBottom()) {
			return null;
		}
		// postop
		var postState = filtered.apply(postOp, action);
		GuardedInterferenceDomain.postoperatorCalls++;

		// TODO: sound?
		if (postState.getStates().isEmpty() || postState.isBottom()) {
			return null;
		}
		// remove local variables of other state we added earlier
		final var missingLocals = DataStructureUtils.difference(interferingState.getVariables(),
				globalTargetState.getVariables());
		if (!missingLocals.isEmpty()) {
			postState = postState.removeVariables(missingLocals);
		}
		/*
		 * Rename our old local program variables, to get the real state of our local variables back. (which cannot
		 * change based on an interference, local vars are not accessible).
		 */
		if (isSelfInterfering) {
			for (final IProgramVarOrConst tempVar : reverseRenamedMap.keySet()) {
				postState = postState.renameVariable(tempVar, reverseRenamedMap.get(tempVar));
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

	private static class LocalProgramVarDummy implements ILocalProgramVar {

		private static final long serialVersionUID = 1L;

		public LocalProgramVarDummy() {
		}

		@Override
		public String getIdentifier() {
			throw new UnsupportedOperationException("Dummy var, should not call its methods");
		}

		@Override
		public String getProcedure() {
			throw new UnsupportedOperationException("Dummy var, should not call its methods");
		}

		@Override
		public TermVariable getTermVariable() {
			throw new UnsupportedOperationException("Dummy var, should not call its methods");
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			throw new UnsupportedOperationException("Dummy var, should not call its methods");
		}

		@Override
		public ApplicationTerm getPrimedConstant() {
			throw new UnsupportedOperationException("Dummy var, should not call its methods");
		}

		@Override
		public Term getTerm() {
			throw new UnsupportedOperationException("Dummy var, should not call its methods");
		}
	}

}
