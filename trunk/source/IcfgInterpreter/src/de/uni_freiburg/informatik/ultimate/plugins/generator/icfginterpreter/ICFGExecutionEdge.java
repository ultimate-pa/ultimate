package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArcSolver;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.TermNormalizer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Update;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;

public class ICFGExecutionEdge {
	public final IcfgLocation source;
	public final IcfgLocation target;
	private final UnmodifiableTransFormula transFormula;
	private final ArrayList<ICFGExecutionEdge> children = new ArrayList<>();
	private final ArrayList<ICFGExecutionEdge> parents = new ArrayList<>();
	/**
	 * The set of all edges where a path exists from this egde to it. If it includes this edge, there is a loop.
	 */
	private final HashSet<ICFGExecutionEdge> reachable = new HashSet<>();
	private final HashSet<ICFGExecutionEdge> ancestors = new HashSet<>();
	private final HashMap<TermVariable, Variable> variables;
	private final ArrayList<ArcSolver> arcSolvers;
	private final HashSet<Variable> outVars;
	private final HashSet<Variable> inVars;
	private final OrTerm guardTerm;

	public ICFGExecutionEdge(final UnmodifiableTransFormula mTransFormula, final IcfgLocation mSource,
			final IcfgLocation mTarget, final ManagedScript managedScript, final IUltimateServiceProvider service) {
		// System.out.println(transFormula.getFormula().toString());
		transFormula = mTransFormula;
		source = mSource;
		target = mTarget;
		variables = TermNormalizer.getVariables(transFormula);

		outVars = new HashSet<>();
		inVars = new HashSet<>();
		for (final Variable var : variables.values()) {
			final VariableTerm termVar = var.getVariableTerm();
			if (termVar.isOutVar) {
				outVars.add(var);
			}
			if (termVar.isInVar) {
				inVars.add(var);
			}
		}

		final ExecutionTerm fullTerm = TermNormalizer.parseTerm(transFormula.getFormula(), variables);
		// final Term convertedTerm = fullTerm.toSMTTerm();
		// final Term originalTerm = transFormula.getFormula();
		// assert SmtUtils.areFormulasEquivalent(originalTerm, convertedTerm, managedScript.getScript());
		final OrTerm outerTerm = TermNormalizer.normalize((BooleanTerm) fullTerm);
		// System.out.println(outerTerm + "\n");
		// assert SmtUtils.areFormulasEquivalent(originalTerm, outerTerm.toSMTTerm(), managedScript.getScript());

		final UnmodifiableTransFormula guardFormula = TransFormulaUtils.computeGuard(mTransFormula, managedScript,
				service);
		guardTerm = TermNormalizer
				.normalize((BooleanTerm) TermNormalizer.parseTerm(guardFormula.getFormula(), variables));

		final ArrayList<BooleanTerm> andTerms = outerTerm.getSubTerms();

		arcSolvers = new ArrayList<>();

		// constraintLists = new AndTerm[andTerms.size()];
		for (final BooleanTerm child : andTerms) {
			final AndTerm andChild = (AndTerm) child;

			arcSolvers.add(new ArcSolver(andChild, managedScript, variables, inVars, outVars, service));
		}

		System.out.println("Full term:");
		System.out.println(outerTerm);
		System.out.println(this + "\n\n\n");
	}

	public void execute(final ProgramState state) {
		// TODO Create and check each arcs guard

	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		out.append("Edge from ").append(source).append(" to ").append(target);
		out.append("\nFormula: ").append(transFormula.getFormula());
		for (final Variable var : variables.values()) {
			out.append("\n").append(var.getVariableTerm());
		}
		out.append("\nGuard:\n").append(guardTerm);

		int i = 0;
		for (final ArcSolver child : arcSolvers) {
			out.append("\nArc ").append(i + 1).append(":\n");
			out.append("  ").append(child.toString().replace("\n", "\n  "));

			final Update[] updates = arcSolvers.get(i).makeUpdates();
			if (updates.length > 0) {
				out.append("\nArc Updates");
			}
			for (final Update update : updates) {
				out.append("\n  ").append(update);
			}
			i++;
		}

		return out.toString();
	}

	public boolean canBeTaken(final ProgramState state) {
		return guardTerm.evaluate(state);
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
		ancestors.add(parent);
		propagateAncestors(parent.ancestors);
	}

	private void propagateAncestors(final HashSet<ICFGExecutionEdge> mAncestors) {
		ancestors.addAll(mAncestors);

		for (final ICFGExecutionEdge child : children) {
			if (child.ancestors.containsAll(ancestors)) {
				continue;
			}
			child.propagateAncestors(ancestors);
		}
	}

	private void propagateReachable(final HashSet<ICFGExecutionEdge> mReachable) {
		reachable.addAll(mReachable);

		for (final ICFGExecutionEdge parent : parents) {
			if (parent.reachable.containsAll(reachable)) {
				continue;
			}
			parent.propagateReachable(reachable);
		}
	}

	public ArrayList<ICFGExecutionEdge> getParents() {
		return Util.copyList(parents);
	}

	public HashSet<ICFGExecutionEdge> getAncestors() {
		return Util.copySet(ancestors);
	}

	public boolean isInLoop() {
		return reachable.contains(this);
	}
}
