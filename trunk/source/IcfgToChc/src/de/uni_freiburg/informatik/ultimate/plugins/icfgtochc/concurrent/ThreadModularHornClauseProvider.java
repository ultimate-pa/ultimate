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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IcfgToChcConcurrent.IHcReplacementVar;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences.IcfgToChcPreferences;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Generates Horn clauses for a thread-modular proof.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class ThreadModularHornClauseProvider extends ExtensibleHornClauseProvider {
	private static final String FUNCTION_NAME = "Inv";
	private static final int INTERFERING_INSTANCE_ID = -1;

	protected final IIcfg<?> mIcfg;
	protected final IcfgToChcPreferences mPrefs;
	private final IIcfgSymbolTable mCfgSymbolTable;
	private final Predicate<IProgramVar> mVariableFilter;

	// maps a procedure name and a location (in the procedure) to an integer, such that the location variable has this
	// integer as value iff control is in the given location
	private final NestedMap2<String, IcfgLocation, Integer> mLocationIndices = new NestedMap2<>();

	// used as location for threads that are not currently running
	private final Term mBottomLocation;

	protected final Set<String> mTemplates;
	protected final List<ThreadInstance> mInstances;
	protected final Set<String> mUnboundedTemplates;

	protected final PredicateInfo mInvariantPredicate;

	protected final Set<HcGlobalVar> mGlobalVars = new HashSet<>();
	protected final Map<ThreadInstance, List<IHcThreadSpecificVar>> mThreadSpecificVars = new HashMap<>();
	protected final Map<ThreadInstance, HcLocationVar> mLocationVars = new HashMap<>();
	protected final NestedMap2<ThreadInstance, IProgramVar, HcLocalVar> mLocalVars = new NestedMap2<>();

	public ThreadModularHornClauseProvider(final ManagedScript mgdScript, final IIcfg<?> icfg,
			final HcSymbolTable symbolTable, final IcfgToChcPreferences prefs) {
		this(mgdScript, icfg, symbolTable, x -> true, prefs);
	}

	public ThreadModularHornClauseProvider(final ManagedScript mgdScript, final IIcfg<?> icfg,
			final HcSymbolTable symbolTable, final Predicate<IProgramVar> variableFilter,
			final IcfgToChcPreferences prefs) {
		super(mgdScript, symbolTable);
		mIcfg = icfg;
		mPrefs = prefs;
		mCfgSymbolTable = mIcfg.getCfgSmtToolkit().getSymbolTable();
		mVariableFilter = variableFilter;

		final var threadInfo =
				mPrefs.concurrencyMode().getThreadNumbersAndUnboundedThreads(icfg, mPrefs.getThreadModularProofLevel());
		mTemplates = Set.copyOf(threadInfo.getFirst().keySet());
		mInstances = getInstances(threadInfo.getFirst());
		mUnboundedTemplates = threadInfo.getSecond();

		mBottomLocation = numeral(-1);
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

		final var paramMap = IntStream.range(0, parameters.size()).mapToObj(i -> new Pair<>(parameters.get(i), i))
				.collect(Collectors.toMap(Pair::getKey, Pair::getValue, (i, j) -> i, BidirectionalMap::new));

		return new PredicateInfo(predicate, paramMap);
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

		final var location = new HcLocationVar(instance, getIntSort());
		mLocationVars.put(instance, location);
		result.add(location);

		final List<IProgramVar> localVars = mCfgSymbolTable.getLocals(instance.getTemplateName()).stream()
				.filter(mVariableFilter).collect(Collectors.toList());
		for (final IProgramVar pv : localVars) {
			final var local = new HcLocalVar(pv, instance.getInstanceNumber());
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

		final var initialClause = buildInitialClause();
		result.add(initialClause);

		final var entryNodes = mIcfg.getProcedureEntryNodes();
		for (final String proc : mTemplates) {
			final IcfgEdgeIterator edges = new IcfgEdgeIterator(entryNodes.get(proc).getOutgoingEdges());
			while (edges.hasNext()) {
				final IcfgEdge edge = edges.next();
				for (final var prePost : getCartesianPrePostProduct(edge)) {
					final var clause =
							buildInductivityClause(edge, prePost.getFirst(), prePost.getSecond(), prePost.getThird());
					result.add(clause);
				}

				if (mUnboundedTemplates.contains(proc)) {
					result.add(buildNonInterferenceClause(edge));
				}
			}
		}

		final var errorLocs = getErrorLocations();
		for (final var pair : errorLocs) {
			final var safetyClause = buildSafetyClause(pair.getFirst(), pair.getSecond());
			result.add(safetyClause);
		}

		return result;
	}

	private List<Triple<Map<ThreadInstance, IcfgLocation>, Map<ThreadInstance, IcfgLocation>, ThreadInstance>>
			getCartesianPrePostProduct(final IcfgEdge edge) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
			final var forkCurrent = (IIcfgForkTransitionThreadCurrent<?>) edge;
			final var forkEntry = mIcfg.getProcedureEntryNodes().get(forkCurrent.getNameOfForkedProcedure());
			final var result =
					new ArrayList<Triple<Map<ThreadInstance, IcfgLocation>, Map<ThreadInstance, IcfgLocation>, ThreadInstance>>();
			for (final var instance : getInstances(edge.getPrecedingProcedure())) {
				final var preds = Map.of(instance, edge.getSource());
				for (final var forked : getInstances(forkCurrent.getNameOfForkedProcedure())) {
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
			assert false : "Joins not supported";
		}

		return getInstances(edge.getPrecedingProcedure()).stream()
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

	// Horn clause generation
	// -----------------------------------------------------------------------------------------------------------------

	/**
	 * Builds the initial clause that encodes the precondition. By default, this method only fixes the initial location
	 * of the threads.
	 */
	protected HornClauseBuilder buildInitialClause() {
		final var clause = createBuilder(mInvariantPredicate, "initial clause");

		// add location constraints
		final var initialLocs = getInitialLocations();
		for (final var instance : mInstances) {
			// If instance does not have an initial location, a constraint for mBottomLocation is added.
			addOutLocationConstraint(clause, instance, initialLocs.get(instance));
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
	protected HornClauseBuilder buildSafetyClause(final ThreadInstance thread, final IcfgLocation errorLoc) {
		// create a clause with head "false"
		final var clause = createBuilder("safety clause for location " + errorLoc + " in thread instance " + thread);

		// add body clause
		clause.addBodyPredicate(mInvariantPredicate, clause.getDefaultBodyArgs(mInvariantPredicate));

		// location constraints
		addInLocationConstraint(clause, thread, errorLoc);

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
	protected HornClauseBuilder buildInductivityClause(final IIcfgTransition<?> transition,
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

	/**
	 * Builds a noninterference clause for the given transition.
	 */
	protected HornClauseBuilder buildNonInterferenceClause(final IIcfgTransition<?> transition) {
		final var clause = createBuilder(mInvariantPredicate, "non-interference clause for transition "
				+ transition.hashCode() + " with transformula " + transition.getTransformula());

		// TODO support transitions with multiple predecessors (joins)
		final var interferingThread = getInterferingThread(transition);

		// add interference-free clause to body
		clause.addBodyPredicate(mInvariantPredicate, clause.getDefaultBodyArgs(mInvariantPredicate));

		// add precondition clauses
		for (final var instance : getInstances(interferingThread.getTemplateName())) {
			final var bodyArgs = clause.getDefaultBodyArgs(mInvariantPredicate);

			// replace thread-specific variables with those for the interfering thread
			final var instanceVars = mThreadSpecificVars.get(instance);
			final var interferingVars = createThreadSpecificVars(interferingThread);
			for (int i = 0; i < instanceVars.size(); ++i) {
				final var original = instanceVars.get(i);
				final var replaced = interferingVars.get(i);
				if (mInvariantPredicate.hasParameter(original)) {
					final int index = mInvariantPredicate.getIndex(original);
					bodyArgs.set(index, clause.getBodyVar(replaced).getTerm());
				}
			}

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

	// Auxiliary methods
	// -----------------------------------------------------------------------------------------------------------------

	protected Map<ThreadInstance, IcfgLocation> getInitialLocations() {
		return mPrefs.concurrencyMode().getInitialLocations(mIcfg, mInstances);
	}

	protected void addInLocationConstraint(final HornClauseBuilder clause, final ThreadInstance threadInstance,
			final IcfgLocation location) {
		final var locTerm =
				location == null ? mBottomLocation : getLocIndexTerm(location, threadInstance.getTemplateName());
		final HcLocationVar locVar = mLocationVars.get(threadInstance);
		final Term term = clause.getBodyVar(locVar).getTerm();
		clause.addConstraint(SmtUtils.binaryEquality(mScript, term, locTerm));
	}

	protected void addOutLocationConstraint(final HornClauseBuilder clause, final ThreadInstance threadInstance,
			final IcfgLocation location) {
		final var locTerm =
				location == null ? mBottomLocation : getLocIndexTerm(location, threadInstance.getTemplateName());
		final HcLocationVar locVar = mLocationVars.get(threadInstance);
		final Term term = clause.getHeadVar(locVar).getTerm();
		clause.addConstraint(SmtUtils.binaryEquality(mScript, term, locTerm));
	}

	protected Term getLocIndexTerm(final IcfgLocation loc, final String proc) {
		Integer index = mLocationIndices.get(proc, loc);
		if (index == null) {
			final Map<IcfgLocation, Integer> otherIndices = mLocationIndices.get(proc);
			index = otherIndices == null ? 0 : otherIndices.size();
			mLocationIndices.put(proc, loc, index);
		}
		return numeral(index);
	}

	protected void addTransitionConstraint(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final ThreadInstance updatedThread, final Collection<HcLocalVar> localVariables) {
		final var tf = transition.getTransformula();
		final var substitution = new HashMap<TermVariable, Term>();

		// deal with global variables
		for (final var global : mGlobalVars) {
			prepareSubstitution(clause, transition, substitution, global, global.getVariable(), true);
		}

		// deal with local variables
		for (final HcLocalVar local : localVariables) {
			final var updatable = local.getThreadInstance().equals(updatedThread);
			prepareSubstitution(clause, transition, substitution, local, local.getVariable(), updatable);
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

	private static void prepareSubstitution(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final Map<TermVariable, Term> substitution, final IHcReplacementVar rv, final IProgramVar pv,
			final boolean canBeUpdated) {
		final var tf = transition.getTransformula();

		final TermVariable inVar = tf.getInVars().get(pv);
		if (inVar != null) {
			substitution.put(inVar, clause.getBodyVar(rv).getTerm());
		}

		final TermVariable outVar = tf.getOutVars().get(pv);
		if (outVar != null && !Objects.equals(inVar, outVar)) {
			substitution.put(outVar, clause.getHeadVar(rv).getTerm());
		}

		if (canBeUpdated && tf.getAssignedVars().contains(pv)) {
			clause.differentBodyHeadVar(rv);
		}
	}

	protected ThreadInstance getInterferingThread(final IIcfgTransition<?> transition) {
		return new ThreadInstance(transition.getPrecedingProcedure(), INTERFERING_INSTANCE_ID);
	}

	private Stream<HcLocalVar> getInterferingLocals(final ThreadInstance interferingThread) {
		return mCfgSymbolTable.getLocals(interferingThread.getTemplateName()).stream().filter(mVariableFilter)
				.map(pv -> new HcLocalVar(pv, INTERFERING_INSTANCE_ID));
	}
}
