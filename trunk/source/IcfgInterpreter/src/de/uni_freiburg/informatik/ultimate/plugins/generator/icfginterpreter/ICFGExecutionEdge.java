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
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.TermNormalizer;
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
	// private final ArrayList<ArcSolver> arcSolvers = new ArrayList<>();
	private final HashSet<TermVariable> outVars;
	private final HashSet<TermVariable> inVars;

	public ICFGExecutionEdge(final UnmodifiableTransFormula mTransFormula, final IcfgLocation mSource,
			final IcfgLocation mTarget, final ManagedScript managedScript, final IUltimateServiceProvider service) {
		// System.out.println(transFormula.getFormula().toString());
		transFormula = mTransFormula;
		source = mSource;
		target = mTarget;
		variables = TermNormalizer.getVariables(transFormula);

		final ExecutionTerm fullTerm = TermNormalizer.parseTerm(transFormula.getFormula(), variables);
		final OrTerm outerTerm = TermNormalizer.normalize((BooleanTerm) fullTerm);
		// System.out.println(outerTerm + "\n");

		final UnmodifiableTransFormula guardFormula = TransFormulaUtils.computeGuard(mTransFormula, managedScript,
				service);
		final ExecutionTerm guardTerm = TermNormalizer.parseTerm(guardFormula.getFormula(), variables);
		final OrTerm outerGuardTerm = TermNormalizer.normalize((BooleanTerm) guardTerm);

		final ArrayList<Variable> vars = new ArrayList<>(variables.values());
		final ArrayList<BooleanTerm> andTerms = outerTerm.getSubTerms();
		// constraintLists = new AndTerm[andTerms.size()];
		for (final BooleanTerm child : andTerms) {
			assert child instanceof AndTerm;
			final AndTerm andChild = (AndTerm) child;

			// arcSolvers.add(new ArcSolver(andChild.getSubTerms(), vars));
			// System.out.println(arcSolver);

		}

		outVars = new HashSet<>();
		inVars = new HashSet<>();
		for (final Variable var : vars) {
			final VariableTerm termVar = var.getVariableTerm();
			final TermVariable programVar = termVar.termvar;
			if (termVar.isOutVar) {
				outVars.add(programVar);
			}
			if (termVar.isInVar) {
				inVars.add(programVar);
			}
		}
	}

	/**
	 * Get a list of all (program variable, domain) pair sets that can be achieved given a list that contains the
	 * domains of the parent ICFGVertexes. If no entry exists for a parent, nothing is calculated.
	 *
	 * @param programDomains
	 * @return / public ArrayList<HashMap<IProgramVar, Domain<?>>> calculateAllDomains(HashMap<IcfgLocation,
	 *         ArrayList<HashMap<IProgramVar, Domain<?>>>> programDomains) { ArrayList<HashMap<IProgramVar, Domain<?>>>
	 *         out = new ArrayList<>();
	 *
	 *         for(ICFGExecutionEdge parent : parents) { ArrayList<HashMap<IProgramVar, Domain<?>>> parentDomains =
	 *         programDomains.getOrDefault(parent.target, null); if(parentDomains == null) { continue; }
	 *         for(HashMap<IProgramVar, Domain<?>> domain : parentDomains) { out.addAll(calculateDomains(domain)); } }
	 *
	 *         return out; }
	 *
	 *         /** Get a list of all sets of (program variable, domain) assignments that each represent a next state,
	 *         such that each can be achieved by applying the transition formula to the given previous state
	 * @param programDomains
	 * @return / public HashSet<HashMap<IProgramVar, Domain<?>>> calculateDomains( final HashMap<IProgramVar, Domain<?>>
	 *         parentDomains) { final HashSet<HashMap<IProgramVar, Domain<?>>> out = new HashSet<>(); for (final
	 *         ArcSolver arcSolver : arcSolvers) { // AndTerm constraint = (AndTerm) child; //
	 *         System.out.println("\nArcs unparsed:\n" + arcy);
	 *
	 *         // HashMap<IProgramVar, Domain<?>> domainsAtSource = definedDomainAt.getOrDefault(sourceVertex, new //
	 *         HashMap<>());
	 *
	 *         /* System.out.println("\nPossible previous values:"); for(Entry<IProgramVar, Domain<?>> entry :
	 *         parentDomains.entrySet()) { if(!inVars.contains(entry.getKey())) { continue; }
	 *         System.out.println(entry.getKey().getGloballyUniqueId() + " in " + entry.getValue()); }
	 */

	// HashMap<IProgramVar, Domain<?>> newDomainsAtTarget = arcy.calculateValidDomains(parentDomains);
	// HashMap<IProgramVar, Domain<?>> oldDomainsAtTarget = definedDomainAt.getOrDefault(target, new
	// HashMap<>());

	/*
	 * System.out.println("\nNew values:"); for(Entry<IProgramVar, Domain<?>> entry : newDomainsAtTarget.entrySet()) {
	 * if(!outVars.contains(entry.getKey()) || !assignableVars.contains(entry.getKey())) { continue; }
	 * System.out.println(entry.getKey().getGloballyUniqueId() + " in " + entry.getValue()); }
	 */

	// combine the possible values of all ways to reach the vertex
	/*
	 * for(Entry<IProgramVar, Domain<?>> current : oldDomainsAtTarget.entrySet()) { Domain<?> newDomain =
	 * newDomainsAtTarget.getOrDefault(current.getKey(), current.getValue()); Domain<?> union =
	 * combineDomains(newDomain, current.getValue()); newDomainsAtTarget.put(current.getKey(), union); } /
	 *
	 * // definedDomainAt.put(target, newDomainsAtTarget);
	 *
	 * // System.out.println(""); out.add(arcSolver.calculateValidDomains(parentDomains)); continue; } return out; }
	 */

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		out.append("Edge from ").append(source).append(" to ").append(target);
		out.append("\nFormula: ").append(transFormula.getFormula());
		for (final Variable var : variables.values()) {
			out.append("\n").append(var.getVariableTerm());
		}
		/*
		 * out.append("\nReachable:"); for(ICFGExecutionEdge edge : reachable) {
		 * out.append("\n  Edge from ").append(edge.source).append(" to ").append(edge.target); }
		 */
		/*
		 * int i = 0; for (final ArcSolver child : arcSolvers) { i++; out.append("\nArc ").append(i).append(":\n");
		 * out.append("  ").append(child.toString().replace("\n", "\n  "));// .append("\n\n"); }
		 */

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
