/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences.IcfgToChcPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences.IcfgToChcPreferences.SpecMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Generates Horn clauses for a thread-modular proof.
 *
 * This class supports two modes of specification: Either we prove absence of assertion violations in all threads, or we
 * prove a precondition-postcondition pair (the postcondition holds once all initially running threads have terminated).
 * The specification mode is set via the preferences (passed to the constructor).
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class ThreadModularHornClauseProvider extends ExtensibleHornClauseProvider {
	private static final String FUNCTION_NAME = "Inv";
	private static final int INTERFERING_INSTANCE_ID = -1;

	protected final IUltimateServiceProvider mServices;
	protected final IIcfg<?> mIcfg;
	protected final IcfgToChcPreferences mPrefs;
	private final IIcfgSymbolTable mCfgSymbolTable;
	private final Predicate<IProgramVar> mVariableFilter;

	// Maps each location to an integer, such that the location variable has this integer as value iff control is in the
	// given location. Locations in different procedures may be mapped to the same value.
	protected final Map<IcfgLocation, Integer> mLocationIndices;

	// used as location for threads that are not currently running
	private final Term mBottomLocation;

	protected final Set<String> mTemplates;
	protected final List<ThreadInstance> mInstances;
	protected final Set<String> mUnboundedTemplates;

	protected final PredicateInfo mInvariantPredicate;

	protected final Set<HcGlobalVar> mGlobalVars = new HashSet<>();
	protected final HcThreadCounterVar mRunningThreadsVar;
	protected final Map<ThreadInstance, List<IHcThreadSpecificVar>> mThreadSpecificVars = new HashMap<>();
	protected final Map<ThreadInstance, HcLocationVar> mLocationVars = new HashMap<>();
	protected final NestedMap2<ThreadInstance, IProgramVar, HcLocalVar> mLocalVars = new NestedMap2<>();

	public ThreadModularHornClauseProvider(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfg<?> icfg, final HcSymbolTable symbolTable, final IcfgToChcPreferences prefs) {
		this(services, mgdScript, icfg, symbolTable, x -> true, prefs);
	}

	public ThreadModularHornClauseProvider(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIcfg<?> icfg, final HcSymbolTable symbolTable, final Predicate<IProgramVar> variableFilter,
			final IcfgToChcPreferences prefs) {
		super(mgdScript, symbolTable);
		mServices = services;
		mIcfg = icfg;
		mPrefs = prefs;
		mCfgSymbolTable = mIcfg.getCfgSmtToolkit().getSymbolTable();
		mVariableFilter = variableFilter;

		final var threadInfo = mPrefs.concurrencyMode().getThreadNumbersAndUnboundedThreads(icfg, mPrefs);
		mTemplates = Set.copyOf(threadInfo.getFirst().keySet());
		mInstances = getInstances(threadInfo.getFirst());
		mUnboundedTemplates = threadInfo.getSecond();

		mLocationIndices = createLocationMap(icfg);
		mBottomLocation = numeral(-1);

		if (mPrefs.specMode() == SpecMode.POSTCONDITION) {
			mRunningThreadsVar = new HcThreadCounterVar(mScript);
		} else {
			mRunningThreadsVar = null;
		}
		mInvariantPredicate = createInvariantPredicate();
	}

	// Initialization code and variable creation
	// -----------------------------------------------------------------------------------------------------------------

	private static List<ThreadInstance> getInstances(final Map<String, Integer> numberOfThreads) {
		final var result = new ArrayList<ThreadInstance>();
		for (final var entry : numberOfThreads.entrySet()) {
			for (int i = 0; i < entry.getValue(); i++) {
				result.add(new ThreadInstance(entry.getKey(), i));
			}
		}
		return result;
	}

	public List<ThreadInstance> getInstances() {
		return mInstances;
	}

	public List<ThreadInstance> getInstances(final String template) {
		return mInstances.stream().filter(inst -> inst.getTemplateName().equals(template)).collect(Collectors.toList());
	}

	private PredicateInfo createInvariantPredicate() {
		final var parameters = getInvariantParameters();

		final List<Sort> sorts = parameters.stream().map(IHcReplacementVar::getSort).collect(Collectors.toList());
		final var predicate = mSymbolTable.getOrConstructHornClausePredicateSymbol(FUNCTION_NAME, sorts);

		return new PredicateInfo(predicate, parameters);
	}

	protected Map<IcfgLocation, Integer> createLocationMap(final IIcfg<?> icfg) {
		final var result = new HashMap<IcfgLocation, Integer>();
		for (final var entry : icfg.getProcedureEntryNodes().entrySet()) {
			final var initial = entry.getValue();

			int counter = 0;
			result.put(initial, counter);
			counter++;

			final var iterator = new IcfgEdgeIterator(initial.getOutgoingEdges());
			while (iterator.hasNext()) {
				final var edge = iterator.next();
				assert result.containsKey(edge.getSource()) : "edge with unknown source loc";
				final var loc = edge.getTarget();

				if (!isRelevantLocation(loc)) {
					continue;
				}

				if (!result.containsKey(loc)) {
					result.put(loc, counter);
					counter++;
				}
			}
		}
		return result;
	}

	// do not map error locations to an integer if they do not appear in the CHC system
	protected boolean isRelevantLocation(final IcfgLocation loc) {
		if (!mPrefs.skipAssertEdges()) {
			return true;
		}
		final var errorNodes = mIcfg.getProcedureErrorNodes().get(loc.getProcedure());
		return errorNodes == null || !errorNodes.contains(loc);
	}

	/**
	 * Constructs the sequence of parameters for the invariant predicate.
	 *
	 * Subclasses can override this method, or more specific methods below ({@link #createGlobalVars()} or
	 * {@link #createThreadSpecificVars(ThreadInstance)}), to add additional parameters.
	 *
	 * @return A (modifiable) list of parameters. The list must not contain duplicates.
	 */
	protected List<IHcReplacementVar> getInvariantParameters() {
		final var result = new ArrayList<IHcReplacementVar>();

		// add variables for thread-modular encoding of postconditions
		if (mPrefs.specMode() == SpecMode.POSTCONDITION) {
			result.add(mRunningThreadsVar);
		}

		result.addAll(createGlobalVars());
		for (final var instance : mInstances) {
			final var threadSpecific = createThreadSpecificVars(instance);
			mThreadSpecificVars.put(instance, threadSpecific);
			result.addAll(threadSpecific);
		}
		return result;
	}

	/**
	 * Constructs those parameters of the invariant predicate that correspond to global variables (used by
	 * {@link #getInvariantParameters()}).
	 *
	 * @return A (modifiable) list of parameters. The list must not contain duplicates.
	 */
	protected List<HcGlobalVar> createGlobalVars() {
		final var result = new ArrayList<HcGlobalVar>();
		for (final var pv : mCfgSymbolTable.getGlobals()) {
			if (mVariableFilter.test(pv)) {
				final var global = new HcGlobalVar(pv);
				mGlobalVars.add(global);
				result.add(global);
			}
		}
		return result;
	}

	/**
	 * Constructs parameters of the invariant predicate that are specific to the given thread instance (used by
	 * {@link #getInvariantParameters()}). By default, this includes local variables of the thread template, and a
	 * location variable (for the program counter).
	 *
	 * @return A (modifiable) list of parameters. The list must not contain duplicates.
	 */
	protected List<IHcThreadSpecificVar> createThreadSpecificVars(final ThreadInstance instance) {
		final var result = new ArrayList<IHcThreadSpecificVar>();

		final var location = new HcLocationVar(instance, mScript);
		mLocationVars.put(instance, location);
		result.add(location);

		final List<IProgramVar> localVars = mCfgSymbolTable.getLocals(instance.getTemplateName()).stream()
				.filter(mVariableFilter).collect(Collectors.toList());
		for (final IProgramVar pv : localVars) {
			final var local = new HcLocalVar(pv, instance);
			mLocalVars.put(instance, pv, local);
			result.add(local);
		}

		return result;
	}

	// IIcfg iteration
	// -----------------------------------------------------------------------------------------------------------------

	@Override
	protected List<HornClauseBuilder> buildAllClauses() {
		final var result = new ArrayList<HornClauseBuilder>();

		// add initial clause
		final var initialClause = buildInitialClause();
		result.add(initialClause);

		// add inductivity and non-interference clauses
		final var entryNodes = mIcfg.getProcedureEntryNodes();
		for (final String proc : mTemplates) {
			final IcfgEdgeIterator edges = new IcfgEdgeIterator(entryNodes.get(proc).getOutgoingEdges());
			while (edges.hasNext()) {
				final IcfgEdge original = edges.next();
				if (!isSkippableAssertEdge(original)) {
					result.addAll(buildClausesForTransition(original));
				}
			}
		}

		// add symmetry clauses, if enabled
		if (mPrefs.useSymmetryClauses()) {
			result.addAll(buildSymmetryClauses());
		}

		// add safety clauses
		switch (mPrefs.specMode()) {
		case ASSERT_VIOLATIONS:
			if (mPrefs.skipAssertEdges()) {
				for (final var triple : getErrorConditions()) {
					final var safetyClause =
							buildErrorSafetyClause(triple.getFirst(), triple.getSecond(), triple.getThird());
					result.add(safetyClause);
				}
			} else {
				for (final var pair : getErrorLocations()) {
					final var safetyClause = buildErrorSafetyClause(pair.getFirst(), pair.getSecond());
					result.add(safetyClause);
				}
			}
			break;
		case POSTCONDITION:
			for (final var thread : getInitialLocations().keySet()) {
				final var safetyClause = buildPostconditionSafetyClause(thread);
				result.add(safetyClause);
			}
			break;
		}

		return result;
	}

	protected List<HornClauseBuilder> buildClausesForTransition(final IcfgEdge original) {
		final var result = new ArrayList<HornClauseBuilder>();

		// replace spec edges by dummy transitions that do nothing (actual constraints are added later)
		IcfgEdge edge;
		if (isPreConditionSpecEdge(original) || isPostConditionSpecEdge(original)) {
			edge = createDummyEdge(original);
		} else {
			edge = original;
		}

		// add inductivity clauses
		for (final var prePost : getCartesianPrePostProduct(edge)) {
			final var clause =
					buildInductivityClause(edge, prePost.getFirst(), prePost.getSecond(), prePost.getThird());
			transformSpecEdgeClause(original, clause);
			result.add(clause);
		}

		// add non-interference clause
		if (mUnboundedTemplates.contains(edge.getPrecedingProcedure())) {
			final var clauses = buildNonInterferenceClauses(edge);
			for (final var clause : clauses) {
				transformSpecEdgeClause(original, clause);
			}
			result.addAll(clauses);
		}

		return result;
	}

	protected IcfgEdge createDummyEdge(final IcfgEdge original) {
		final var tf = TransFormulaBuilder.getTrivialTransFormula(mManagedScript);
		return new IcfgEdge(original.getSource(), original.getTarget(), original.getPayload()) {
			@Override
			public UnmodifiableTransFormula getTransformula() {
				return tf;
			}

			@Override
			public String toString() {
				return "<[ dummy edge: assume true; ]>";
			}
		};
	}

	// add actual constraints for spec edges, do nothing if not a spec edge
	protected void transformSpecEdgeClause(final IcfgEdge edge, final HornClauseBuilder clause) {
		// TODO Fix this for
		// - parametric programs with some single-instance threads:
		// ---> i.e. only modify counter for unbounded templates; make sure bounded threads all at exit loc
		// - parametric programs with multiple unbounded templates:
		// ---> should there be one counter per template?
		// - fork/join programs
		// ---> i.e. we don't need the counter, just assert post after main thread has exited

		if (isPreConditionSpecEdge(edge) && mPrefs.specMode() == SpecMode.POSTCONDITION) {
			incrementThreadCounter(clause, mRunningThreadsVar, 1L);
		} else if (isPostConditionSpecEdge(edge)) {
			incrementThreadCounter(clause, mRunningThreadsVar, -1L);
		}
	}

	protected void incrementThreadCounter(final HornClauseBuilder clause, final HcThreadCounterVar counter,
			final long delta) {
		// add constraint counter' = counter + delta
		clause.differentBodyHeadVar(counter);
		clause.addConstraint(SmtUtils.binaryEquality(mScript, clause.getHeadVar(counter).getTerm(),
				SmtUtils.sum(mScript, getIntSort(), clause.getBodyVar(counter).getTerm(), numeral(delta))));
	}

	protected boolean isPreConditionSpecEdge(final IcfgEdge edge) {
		if (!mPrefs.hasPreconditions()) {
			return false;
		}
		final var template = edge.getPrecedingProcedure();
		final var entryLoc = mIcfg.getProcedureEntryNodes().get(template);
		return edge.getSource().equals(entryLoc);
	}

	protected boolean isPostConditionSpecEdge(final IcfgEdge edge) {
		if (mPrefs.specMode() != SpecMode.POSTCONDITION) {
			return false;
		}
		final var template = edge.getPrecedingProcedure();
		final var exitLoc = mIcfg.getProcedureExitNodes().get(template);
		return edge.getTarget().equals(exitLoc);
	}

	protected boolean isSkippableAssertEdge(final IcfgEdge edge) {
		if (!mPrefs.skipAssertEdges()) {
			return false;
		}
		final var errorLocs = mIcfg.getProcedureErrorNodes().get(edge.getSucceedingProcedure());
		if (errorLocs == null) {
			return false;
		}
		return errorLocs.contains(edge.getTarget());
	}

	private List<ThreadInstance> getCandidateInstancesForClause(final String templateName) {
		if (mPrefs.useSymmetryClauses()) {
			// If symmetry clauses are used, we only generate clauses for the first instance.
			return getInstances(templateName).stream().limit(1L).collect(Collectors.toList());
		}
		// Otherwise we generate clauses for each instance.
		return getInstances(templateName);
	}

	private List<Triple<Map<ThreadInstance, IcfgLocation>, Map<ThreadInstance, IcfgLocation>, ThreadInstance>>
			getCartesianPrePostProduct(final IcfgEdge edge) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
			final var forkCurrent = (IIcfgForkTransitionThreadCurrent<?>) edge;
			final var forkEntry = mIcfg.getProcedureEntryNodes().get(forkCurrent.getNameOfForkedProcedure());
			final var result =
					new ArrayList<Triple<Map<ThreadInstance, IcfgLocation>, Map<ThreadInstance, IcfgLocation>, ThreadInstance>>();
			for (final var instance : getCandidateInstancesForClause(edge.getPrecedingProcedure())) {
				final var preds = Map.of(instance, edge.getSource());
				for (final var forked : getCandidateInstancesForClause(forkCurrent.getNameOfForkedProcedure())) {
					if (Objects.equals(instance, forked)) {
						continue;
					}
					final var succs = Map.of(instance, edge.getTarget(), forked, forkEntry);
					result.add(new Triple<>(preds, succs, instance));
				}
			}
			return result;
		}
		if (edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			throw new UnsupportedOperationException("Joins not supported");
		}

		return getCandidateInstancesForClause(edge.getPrecedingProcedure()).stream()
				.map(t -> new Triple<>(Map.of(t, edge.getSource()), Map.of(t, edge.getTarget()), t))
				.collect(Collectors.toList());
	}

	private List<Pair<ThreadInstance, IcfgLocation>> getErrorLocations() {
		return mIcfg.getProcedureErrorNodes().entrySet().stream()
				.flatMap(e -> e.getValue().stream().map(l -> new Pair<>(e.getKey(), l)))
				.flatMap(e -> mInstances.stream().filter(i -> i.getTemplateName().equals(e.getKey()))
						.<Pair<ThreadInstance, IcfgLocation>> map(i -> new Pair<>(i, e.getValue())))
				.collect(Collectors.toList());
	}

	private List<Triple<ThreadInstance, IcfgLocation, UnmodifiableTransFormula>> getErrorConditions() {
		return mIcfg.getProcedureErrorNodes().entrySet().stream()
				.flatMap(e -> e.getValue().stream().map(l -> new Pair<>(e.getKey(), l)))
				.flatMap(e -> e.getValue().getIncomingEdges().stream()
						.map(t -> new Triple<>(e.getKey(), t.getSource(), t.getTransformula())))
				.flatMap(e -> mInstances.stream().filter(i -> i.getTemplateName().equals(e.getFirst()))
						.<Triple<ThreadInstance, IcfgLocation, UnmodifiableTransFormula>> map(
								i -> new Triple<>(i, e.getSecond(), e.getThird())))
				.collect(Collectors.toList());
	}

	// Horn clause generation
	// -----------------------------------------------------------------------------------------------------------------

	/**
	 * Builds the initial clause that encodes the precondition.
	 */
	protected HornClauseBuilder buildInitialClause() {
		final var clause = createBuilder(mInvariantPredicate, "initial clause");
		final var initialLocs = getInitialLocations();

		// add location constraints
		for (final var instance : mInstances) {
			// If an instance does not have an initial location, a constraint for mBottomLocation is added.
			addOutLocationConstraint(clause, instance, initialLocs.get(instance));
		}

		if (mPrefs.specMode() == SpecMode.POSTCONDITION) {
			// add constraints that thread counter (for thread-modular encoding of postconditions) is initially 0
			clause.addConstraint(
					SmtUtils.binaryEquality(mScript, clause.getHeadVar(mRunningThreadsVar).getTerm(), numeral(0)));
		}

		if (mPrefs.hasPreconditions()) {
			// add precondition constraint
			final var locals = mLocalVars.values().collect(Collectors.toList());
			for (final var entry : initialLocs.entrySet()) {
				// The (only) outgoing edge of the initial location should be an assumption of the precondition
				final var precond = DataStructureUtils
						.getOneAndOnly(entry.getValue().getOutgoingEdges(), "outgoing edge of initial location")
						.getTransformula();
				assert precond.getAssignedVars().isEmpty() : "Precondition must not modify variables";
				addTransitionConstraint(clause, precond, entry.getKey(), locals);
			}
		}

		return clause;
	}

	/**
	 * Builds a safety clause specifying unreachability of a given error location.
	 *
	 * @param thread
	 *            The thread instance which must not reach the error location
	 * @param errorLoc
	 *            The error location that shall be proven unreachable
	 */
	protected HornClauseBuilder buildErrorSafetyClause(final ThreadInstance thread, final IcfgLocation errorLoc) {
		// create a clause with head "false"
		final var clause = createBuilder("safety clause for location " + errorLoc + " in thread instance " + thread);

		// add body clause
		clause.addBodyPredicate(mInvariantPredicate, clause.getDefaultBodyArgs(mInvariantPredicate));

		// location constraints
		addInLocationConstraint(clause, thread, errorLoc);

		return clause;
	}

	protected HornClauseBuilder buildErrorSafetyClause(final ThreadInstance thread, final IcfgLocation loc,
			final UnmodifiableTransFormula guard) {
		// create a clause with head "false"
		final var clause = createBuilder("safety clause for location " + loc + " in thread instance " + thread);

		// add body clause
		clause.addBodyPredicate(mInvariantPredicate, clause.getDefaultBodyArgs(mInvariantPredicate));

		// location constraints
		addInLocationConstraint(clause, thread, loc);

		// add transition guard
		final var locals = mLocalVars.values().collect(Collectors.toList());
		addTransitionConstraint(clause, guard, thread, locals);

		return clause;
	}

	/**
	 * Builds a safety clause specifying that if a given thread exits, and the numbers of started and exited threads are
	 * equal, the postcondition holds.
	 *
	 * @param thread
	 *            The thread for which the clause should be generated. This must be a thread that runs initially.
	 */
	protected HornClauseBuilder buildPostconditionSafetyClause(final ThreadInstance thread) {
		// create a clause with head "false"
		final var clause = createBuilder("safety clause for postcondition in thread instance " + thread);

		// add body clause
		clause.addBodyPredicate(mInvariantPredicate, clause.getDefaultBodyArgs(mInvariantPredicate));

		// location constraints
		final var exitLoc = mIcfg.getProcedureExitNodes().get(thread.getTemplateName());
		addInLocationConstraint(clause, thread, exitLoc);

		// add thread counter constraint: running == 0
		clause.addConstraint(
				SmtUtils.binaryEquality(mScript, clause.getBodyVar(mRunningThreadsVar).getTerm(), numeral(0L)));

		// add negated postcondition
		final var postcondition = DataStructureUtils
				.getOneAndOnly(exitLoc.getIncomingEdges(), "transition to exit location").getTransformula();
		assert postcondition.getAssignedVars().isEmpty() : "postcondition cannot modify variables";
		final var negated = TransFormulaUtils.negate(
				TransFormulaUtils.computeGuard(postcondition, mManagedScript, mServices), mManagedScript, mServices);
		final var locals = mLocalVars.values().collect(Collectors.toList());
		addTransitionConstraint(clause, negated, null, locals);

		return clause;
	}

	/**
	 * Builds an inductivity clause that encodes the effect of a transition on the thread that executes it.
	 *
	 * @param transition
	 *            The transition whose effect is encoded
	 * @param preds
	 *            A map specifying predecessor locations of the transition. Each thread instance involved in the
	 *            transition must have an entry; other thread instances must not.
	 *
	 *            Specifying multiple predecessors can be useful for joins. However, joins are not yet fully supported
	 *            by this class.
	 * @param succs
	 *            A map specifying successor locations of the transition. Each thread instance involved in the
	 *            transition must have an entry; other thread instances must not.
	 *
	 *            Specifying multiple predecessors can be useful for forks.
	 * @param updatedThread
	 *            The primary active thread, whose local variables are updated by the transition.
	 */
	protected HornClauseBuilder buildInductivityClause(final IcfgEdge transition,
			final Map<ThreadInstance, IcfgLocation> preds, final Map<ThreadInstance, IcfgLocation> succs,
			final ThreadInstance updatedThread) {
		final var clause = createBuilder(mInvariantPredicate,
				"inductivity clause for transition " + transition.hashCode() + " with transformula "
						+ transition.getTransformula() + " and thread instance " + updatedThread);

		// add body clause
		clause.addBodyPredicate(mInvariantPredicate, clause.getDefaultBodyArgs(mInvariantPredicate));

		// add location constraints
		for (final var instance : mInstances) {
			final var isActive = preds.containsKey(instance) || succs.containsKey(instance);
			if (isActive) {
				// if instance only in preds or only in succs, the respective other location is mBottomLocation
				clause.differentBodyHeadVar(mLocationVars.get(instance));
				addInLocationConstraint(clause, instance, preds.get(instance));
				addOutLocationConstraint(clause, instance, succs.get(instance));
			}
		}

		// add transition constraint
		final var locals = mLocalVars.values().collect(Collectors.toList());
		addTransitionConstraint(clause, transition, updatedThread, locals);

		return clause;
	}

	protected List<HornClauseBuilder> buildNonInterferenceClauses(final IcfgEdge transition) {
		final var result = new ArrayList<HornClauseBuilder>();
		result.add(buildNonInterferenceClause(transition));
		return result;
	}

	/**
	 * Builds a noninterference clause for the given transition.
	 */
	protected HornClauseBuilder buildNonInterferenceClause(final IcfgEdge transition) {
		// TODO support transitions with multiple predecessors (joins)
		final var interferingThread = getInterferingThread(transition);
		final var interferingVars = createThreadSpecificVars(interferingThread);

		return buildNonInterferenceClause(transition, (clause, instance) -> {
			final var bodyArgs = new ArrayList<>(mInvariantPredicate.getParameters());
			replaceThreadVariables(bodyArgs, instance, interferingVars);
			return bodyArgs.stream().map(v -> clause.getBodyVar(v).getTerm()).collect(Collectors.toList());
		});
	}

	protected HornClauseBuilder buildNonInterferenceClause(final IIcfgTransition<?> transition,
			final BiFunction<HornClauseBuilder, ThreadInstance, List<Term>> getInterferencePrecondition) {
		final var clause = createBuilder(mInvariantPredicate, "non-interference clause for transition "
				+ transition.hashCode() + " with transformula " + transition.getTransformula());

		// TODO support transitions with multiple predecessors (joins)
		final var interferingThread = getInterferingThread(transition);

		// add interference-free clause to body
		clause.addBodyPredicate(mInvariantPredicate, clause.getDefaultBodyArgs(mInvariantPredicate));

		// add precondition clauses
		for (final var instance : getInstances(interferingThread.getTemplateName())) {
			final var bodyArgs = getInterferencePrecondition.apply(clause, instance);
			clause.addBodyPredicate(mInvariantPredicate, bodyArgs);
		}

		// add location constraint
		addInLocationConstraint(clause, interferingThread, transition.getSource());

		// add transition constraint
		final var locals = Stream.concat(mLocalVars.values(), getInterferingLocals(interferingThread))
				.collect(Collectors.toList());
		addTransitionConstraint(clause, transition, interferingThread, locals);

		return clause;
	}

	protected List<HornClauseBuilder> buildSymmetryClauses() {
		final var result = new ArrayList<HornClauseBuilder>();

		final var groups = mInstances.stream().collect(Collectors.groupingBy(ThreadInstance::getTemplateName));
		for (final var group : groups.values()) {
			// skip trivial groups
			if (group.size() <= 1) {
				continue;
			}

			for (int i = 0; i < group.size() - 1; ++i) {
				final var current = group.get(i);
				final var next = group.get(i + 1);
				final var transposition = Map.of(current, next, next, current);
				result.add(buildSymmetryClause(transposition));
			}
		}

		return result;
	}

	protected HornClauseBuilder buildSymmetryClause(final Map<ThreadInstance, ThreadInstance> permutation) {
		final var clause = createBuilder(mInvariantPredicate, "symmetry clause");
		final var bodyArgs = new ArrayList<>(mInvariantPredicate.getParameters());

		for (final var entry : permutation.entrySet()) {
			assert !entry.getKey().equals(entry.getValue()) : "Identity permutations should be omitted";
			assert entry.getKey().getTemplateName()
					.equals(entry.getValue().getTemplateName()) : "Must not permute threads with different templates";
			assert permutation.containsKey(entry.getValue()) : "Not a permutation: " + permutation;
			replaceThreadVariables(bodyArgs, entry.getValue(), mThreadSpecificVars.get(entry.getKey()));
		}

		final var bodyTerms = bodyArgs.stream().map(v -> clause.getBodyVar(v).getTerm()).collect(Collectors.toList());
		clause.addBodyPredicate(mInvariantPredicate, bodyTerms);

		return clause;
	}

	protected void replaceThreadVariables(final List<IHcReplacementVar> parameters, final ThreadInstance oldInstance,
			final List<IHcThreadSpecificVar> newVariables) {
		final var oldVariables = mThreadSpecificVars.get(oldInstance);
		assert oldVariables.size() == newVariables.size();
		for (int i = 0; i < oldVariables.size(); ++i) {
			final var original = oldVariables.get(i);
			final var replaced = newVariables.get(i);
			Collections.replaceAll(parameters, original, replaced);
		}
	}

	// Auxiliary methods
	// -----------------------------------------------------------------------------------------------------------------

	protected Map<ThreadInstance, IcfgLocation> getInitialLocations() {
		return mPrefs.concurrencyMode().getInitialLocations(mIcfg, mInstances, mPrefs);
	}

	protected void addInLocationConstraint(final HornClauseBuilder clause, final ThreadInstance threadInstance,
			final IcfgLocation location) {
		final var locTerm = location == null ? mBottomLocation : getLocIndexTerm(location);
		final HcLocationVar locVar = new HcLocationVar(threadInstance, mScript);
		final Term term = clause.getBodyVar(locVar).getTerm();
		clause.addConstraint(SmtUtils.binaryEquality(mScript, term, locTerm));
	}

	protected void addOutLocationConstraint(final HornClauseBuilder clause, final ThreadInstance threadInstance,
			final IcfgLocation location) {
		final var locTerm = location == null ? mBottomLocation : getLocIndexTerm(location);
		final HcLocationVar locVar = mLocationVars.get(threadInstance);
		final Term term = clause.getHeadVar(locVar).getTerm();
		clause.addConstraint(SmtUtils.binaryEquality(mScript, term, locTerm));
	}

	protected Term getLocIndexTerm(final IcfgLocation loc) {
		final int index = mLocationIndices.get(loc);
		return numeral(index);
	}

	protected void addTransitionConstraint(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final ThreadInstance updatedThread, final Collection<HcLocalVar> localVariables) {
		addTransitionConstraint(clause, transition.getTransformula(), updatedThread, localVariables);
	}

	protected void addTransitionConstraint(final HornClauseBuilder clause, final UnmodifiableTransFormula tf,
			final ThreadInstance updatedThread, final Collection<HcLocalVar> localVariables) {
		final var substitution = new HashMap<TermVariable, Term>();

		// deal with global variables
		for (final var global : mGlobalVars) {
			prepareSubstitution(clause, tf, substitution, global, global.getVariable());
		}

		// deal with local variables
		for (final HcLocalVar local : localVariables) {
			final var updatable = local.getThreadInstance().equals(updatedThread);
			if (updatable) {
				prepareSubstitution(clause, tf, substitution, local, local.getVariable());
			}
		}

		// replace all other variables with auxiliary variables
		final Term formula = tf.getFormula();
		for (final TermVariable v : formula.getFreeVars()) {
			assert substitution.containsKey(v) || tf.getAuxVars().contains(v) : "not an auxiliary variable: " + v;
			substitution.computeIfAbsent(v, variable -> clause.getFreshBodyVar(variable, variable.getSort()).getTerm());
		}

		// add transition constraint
		clause.addConstraint(Substitution.apply(mManagedScript, substitution, formula));
	}

	private static void prepareSubstitution(final HornClauseBuilder clause, final UnmodifiableTransFormula tf,
			final Map<TermVariable, Term> substitution, final IHcReplacementVar rv, final IProgramVar pv) {
		final TermVariable inVar = tf.getInVars().get(pv);
		if (inVar != null) {
			substitution.put(inVar, clause.getBodyVar(rv).getTerm());
		}

		final TermVariable outVar = tf.getOutVars().get(pv);
		final var dummyOutVars = new HashMap<IHcReplacementVar, HcBodyVar>();
		if (outVar != null && !Objects.equals(inVar, outVar)) {
			final var headPred = clause.getHeadPredicate();
			if (headPred != null && headPred.hasParameter(rv)) {
				substitution.put(outVar, clause.getHeadVar(rv).getTerm());
			} else {
				final var bodyVar = dummyOutVars.computeIfAbsent(rv, x -> clause.getFreshBodyVar(x, x.getSort()));
				substitution.put(outVar, bodyVar.getTerm());
			}
		}

		if (tf.getAssignedVars().contains(pv)) {
			clause.differentBodyHeadVar(rv);
		}
	}

	protected ThreadInstance getInterferingThread(final IIcfgTransition<?> transition) {
		return new ThreadInstance(transition.getPrecedingProcedure(), INTERFERING_INSTANCE_ID);
	}

	protected Stream<HcLocalVar> getInterferingLocals(final ThreadInstance interferingThread) {
		return mCfgSymbolTable.getLocals(interferingThread.getTemplateName()).stream().filter(mVariableFilter)
				.map(pv -> new HcLocalVar(pv, interferingThread));
	}
}
