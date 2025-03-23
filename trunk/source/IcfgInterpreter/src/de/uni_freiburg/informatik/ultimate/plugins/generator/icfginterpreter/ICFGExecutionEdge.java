package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArcSolver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.TermNormalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Update;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.FalseTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.TrueTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class ICFGExecutionEdge {
	public final IcfgLocation mSource;
	public final IcfgLocation mTarget;
	private final UnmodifiableTransFormula mTransFormula;
	private final ArrayList<ICFGExecutionEdge> children = new ArrayList<>();
	private final ArrayList<ICFGExecutionEdge> parents = new ArrayList<>();
	/**
	 * The set of all edges where a path exists from this egde to it. If it includes this edge, there is a loop.
	 */
	private final HashSet<ICFGExecutionEdge> mReachable = new HashSet<>();
	private final HashSet<ICFGExecutionEdge> mAncestors = new HashSet<>();
	private final HashMap<TermVariable, Variable> mVariables;
	private final ArcSolver mArcSolver;
	private final OrTerm mGuardTerm;

	private ICFGExecutionEdge(final UnmodifiableTransFormula transFormula, final IcfgLocation source,
			final IcfgLocation target, final HashMap<TermVariable, Variable> variables, final ArcSolver arcSolver,
			final OrTerm guardTerm) {
		mTransFormula = transFormula;
		mSource = source;
		mTarget = target;
		mVariables = variables;
		mArcSolver = arcSolver;
		mGuardTerm = guardTerm;
	}

	/**
	 * Creates edges representing each path through this transition should there be more than one (in DNF form achieved
	 * by {@link TermNormalizer#simplifyToDNF(BooleanTerm)}
	 *
	 * @param transFormula
	 * @param source
	 * @param target
	 * @param managedScript
	 * @param service
	 * @return
	 */
	public static ArrayList<ICFGExecutionEdge> createEdges(final UnmodifiableTransFormula transFormula,
			final IcfgLocation source, final IcfgLocation target, final ManagedScript managedScript,
			final IUltimateServiceProvider service) {
		final HashMap<TermVariable, Variable> variables = TermNormalizer.getVariables(transFormula);

		final HashSet<Variable> outVars = new HashSet<>();
		final HashSet<Variable> inVars = new HashSet<>();
		for (final Variable var : variables.values()) {
			final VariableTerm termVar = var.getVariableTerm();
			if (termVar.isOutVar) {
				outVars.add(var);
			}
			if (termVar.isInVar) {
				inVars.add(var);
			}
		}

		final Term formula = transFormula.getFormula();
		final Theory formulaTheory = formula.getTheory();
		final ExecutionTerm fullTerm = TermNormalizer.parseTerm(formula, variables);
		final OrTerm outerTerm = TermNormalizer.simplifyToDNF((BooleanTerm) fullTerm);

		final UnmodifiableTransFormula guardFormula = TransFormulaUtils.computeGuard(transFormula, managedScript,
				service);
		final OrTerm guardTerm = TermNormalizer
				.simplifyToDNF((BooleanTerm) TermNormalizer.parseTerm(guardFormula.getFormula(), variables));

		if (falseGuard.equals(guardTerm)) {
			return new ArrayList<>(); // edge can never be taken, no need to return it for execution
		}

		final ArrayList<BooleanTerm> andTerms = outerTerm.getSubTerms();

		final HashMap<ArcSolver, AndTerm> arcSolvers = new HashMap<>();

		int constrainingArcs = 0;
		for (final BooleanTerm child : andTerms) {
			final AndTerm andChild = (AndTerm) child;
			final ArcSolver newSolver = new ArcSolver(andChild, managedScript, variables, inVars, outVars, service,
					formulaTheory);
			constrainingArcs += newSolver.hasConstraints() ? 1 : 0;
			arcSolvers.put(newSolver, andChild);
		}

		// System.out.println("Full term:");
		// System.out.println(outerTerm);

		final ArrayList<ICFGExecutionEdge> edges = new ArrayList<>();
		if (constrainingArcs == 0) {
			// all ways to the next state have no updates, make trivial arc with the guard of the whole term
			final ArcSolver trivialArc = new ArcSolver(new AndTerm(new TrueTerm()), managedScript, variables, inVars,
					outVars, service, formulaTheory);
			edges.add(new ICFGExecutionEdge(transFormula, source, target, variables, trivialArc, guardTerm));

			// System.out.println(edges.get(0));
			// System.out.println("\n\n\n");
			return edges;
		}

		final Infeasibility isInfeasable = guardFormula.isInfeasible();
		final Set<TermVariable> branchEncoders = guardFormula.getBranchEncoders();
		for (final Entry<ArcSolver, AndTerm> entry : arcSolvers.entrySet()) {
			final UnmodifiableTransFormula arcGuardFormula = entry.getKey().makeGuardFormula(managedScript, service,
					entry.getValue().toSMTTerm(formulaTheory), isInfeasable, branchEncoders);
			final OrTerm arcGuardTerm = TermNormalizer
					.simplifyToDNF((BooleanTerm) TermNormalizer.parseTerm(arcGuardFormula.getFormula(), variables));

			if (falseGuard.equals(arcGuardTerm)) {
				continue; // edge can never be taken, no need to return it for execution
			}

			final ICFGExecutionEdge newEdge = new ICFGExecutionEdge(transFormula, source, target, variables,
					entry.getKey(), arcGuardTerm);
			// System.out.println(newEdge);
			edges.add(newEdge);
		}
		// System.out.println("\n\n\n");
		return edges;
	}

	private static final OrTerm falseGuard = new OrTerm(new AndTerm(new FalseTerm()));

	public ProgramState execute(final ProgramState currentState, final NonDeterministicChoice ndc) {
		final ProgramState nextState = currentState.clone();
		final Update[] updates = mArcSolver.makeUpdates();
		for (final Update update : updates) {
			update.apply(currentState, nextState, ndc);
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
		out.append("\nFormula: ").append(mTransFormula.getFormula());
		for (final Variable var : mVariables.values()) {
			out.append("\n").append(var.getVariableTerm());
		}
		out.append("\nGuard:\n").append(mGuardTerm);

		final Update[] updates = mArcSolver.makeUpdates();
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

	public void addChildren(final ArrayList<ICFGExecutionEdge> mChildren) {
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
		return Util.copyList(parents);
	}

	public ArrayList<ICFGExecutionEdge> getChildren() {
		return Util.copyList(children);
	}

	public HashSet<ICFGExecutionEdge> getAncestors() {
		return Util.copySet(mAncestors);
	}

	public ArrayList<Variable> getVariables() {
		return new ArrayList<>(mVariables.values());
	}

	/**
	 * Get all variables that can appear in this edge or any edge reachable from this edge
	 *
	 * @return
	 */
	public ArrayList<Variable> getReachableVariables() {
		final HashSet<Variable> out = new HashSet<>(mVariables.values());

		for (final ICFGExecutionEdge reachable : mReachable) {
			out.addAll(reachable.mVariables.values());
		}

		return new ArrayList<>(out);
	}

	public boolean isInLoop() {
		return mReachable.contains(this);
	}
}
