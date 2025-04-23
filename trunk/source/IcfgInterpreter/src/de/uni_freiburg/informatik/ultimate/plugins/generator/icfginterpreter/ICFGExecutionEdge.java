package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArcSolver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Update;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.VariableSet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class ICFGExecutionEdge {
	public final IcfgLocation mSource;
	public final IcfgLocation mTarget;
	private final UnmodifiableTransFormula mTransFormula;
	private final HashSet<ICFGExecutionEdge> children = new HashSet<>();
	private final HashSet<ICFGExecutionEdge> parents = new HashSet<>();
	/**
	 * The set of all edges where a path exists from this edge to it. If it includes this edge, there is a loop.
	 */
	private final HashSet<ICFGExecutionEdge> mReachable = new HashSet<>();
	private final HashSet<ICFGExecutionEdge> mAncestors = new HashSet<>();
	private final VariableSet mVariables;
	private final ArcSolver mArcSolver;
	private final OrTerm mGuardTerm;
	private final String mIndentifier;

	public final UnmodifiableTransFormula mGuardFormula;

	public ICFGExecutionEdge(final UnmodifiableTransFormula transFormula, final UnmodifiableTransFormula guardFormula,
			final IcfgLocation source, final IcfgLocation target, final VariableSet variables,
			final ArcSolver arcSolver, final OrTerm guardTerm, final String identifier) {
		mTransFormula = transFormula;
		mGuardFormula = guardFormula;
		mSource = source;
		mTarget = target;
		mVariables = variables;
		mArcSolver = arcSolver;
		mGuardTerm = guardTerm;
		mIndentifier = identifier;
	}

	public ProgramState execute(final ProgramState currentState) {
		final ProgramState nextState = currentState.clone();
		final Update[] updates = mArcSolver.getUpdates();
		for (final Update update : updates) {
			update.apply(currentState, nextState);
		}
		nextState.finalizeState();
		return nextState;
	}

	public boolean canBeTaken(final ProgramState currentState) {
		return mGuardTerm.evaluate(currentState, currentState); // guard should contain no outVars
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		out.append("Edge from ").append(mSource).append(" to ").append(mTarget);
		out.append("\nFormula: ").append(mTransFormula.getFormula().toStringDirect());
		for (final Variable var : mVariables.getVariables()) {
			out.append("\n").append(var.getVariableTerm());
		}
		out.append("\nGuard:\n").append(mGuardTerm);

		final Update[] updates = mArcSolver.getUpdates();
		if (updates.length > 0) {
			out.append("\nUpdates:");
			for (final Update update : updates) {
				out.append("\n  ").append(update);
			}
		} else {
			out.append("\nNo updates.");
		}

		return out.toString();
	}

	public Update[] getUpdates() {
		return mArcSolver.getUpdates();
	}

	public OrTerm getGuard() {
		return mGuardTerm;
	}

	public void addChildren(final Collection<ICFGExecutionEdge> mChildren) {
		children.addAll(mChildren);

		for (final ICFGExecutionEdge child : mChildren) {
			child.addParent(this);
		}

		propagateReachable(new HashSet<>(mChildren));
	}

	private void addParent(final ICFGExecutionEdge parent) {
		parents.add(parent);
		mAncestors.add(parent);
		propagateAncestors(parent.mAncestors);
	}

	private void propagateAncestors(final HashSet<ICFGExecutionEdge> ancestors) {
		mAncestors.addAll(ancestors);

		for (final ICFGExecutionEdge child : children) {
			if (child.mAncestors.containsAll(mAncestors)) {
				continue;
			}
			child.propagateAncestors(mAncestors);
		}
	}

	private void propagateReachable(final HashSet<ICFGExecutionEdge> reachable) {
		mReachable.addAll(reachable);

		for (final ICFGExecutionEdge parent : parents) {
			if (parent.mReachable.containsAll(mReachable)) {
				continue;
			}
			parent.propagateReachable(mReachable);
		}
	}

	public UnmodifiableTransFormula getTransFormula() {
		return mTransFormula;
	}

	public ArrayList<ICFGExecutionEdge> getParents() {
		return new ArrayList<>(parents);
	}

	public ArrayList<ICFGExecutionEdge> getChildren() {
		return new ArrayList<>(children);
	}

	public HashSet<ICFGExecutionEdge> getAncestors() {
		return Util.copySet(mAncestors);
	}

	public HashSet<Variable> getVariables() {
		return mVariables.getVariables();
	}

	/**
	 * Get all variables that can appear in this edge or any edge reachable from this edge
	 *
	 * @return
	 */
	public ArrayList<Variable> getReachableVariables() {
		final HashSet<Variable> out = mVariables.getVariables();

		for (final ICFGExecutionEdge reachable : mReachable) {
			out.addAll(reachable.mVariables.getVariables());
		}

		return new ArrayList<>(out);
	}

	public boolean isInLoop() {
		return mReachable.contains(this);
	}

	public String getUniqueName() {
		return mSource.toString() + "_To_" + mTarget.toString() + "_" + mIndentifier;
	}
}
