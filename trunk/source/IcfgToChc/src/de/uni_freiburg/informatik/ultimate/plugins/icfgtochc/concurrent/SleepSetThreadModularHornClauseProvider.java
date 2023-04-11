/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetThreadModularHornClauseProvider extends ThreadModularHornClauseProvider {
	private final IIndependenceRelation<?, ? super IIcfgTransition<?>> mIndependence;
	private final Map<String, Collection<IcfgLocation>> mThreadLocations;

	private final Map<ThreadInstance, HcThreadIdVar> mIdVars;
	private final Map<ThreadInstance, HcSleepVar> mSleepVars;

	public SleepSetThreadModularHornClauseProvider(final Map<String, Integer> numberOfThreads,
			final ManagedScript mgdScript, final CfgSmtToolkit cfgSmtToolkit, final HcSymbolTable symbolTable,
			final Predicate<IProgramVar> variableFilter,
			final IIndependenceRelation<?, ? super IIcfgTransition<?>> independence,
			final Map<String, Collection<IcfgLocation>> threadLocations) {
		super(numberOfThreads, mgdScript, cfgSmtToolkit, symbolTable, variableFilter);
		mIndependence = independence;
		mThreadLocations = threadLocations;

		mIdVars = extractThreadVars(HcThreadIdVar.class);
		mSleepVars = extractThreadVars(HcSleepVar.class);
	}

	private <V> Map<ThreadInstance, V> extractThreadVars(final Class<V> varClass) {
		return mThreadSpecificVars.entrySet().stream()
				.map(entry -> new Pair<>(entry.getKey(),
						entry.getValue().stream().filter(varClass::isInstance).map(varClass::cast).findFirst().get()))
				.collect(Collectors.toMap(Pair::getKey, Pair::getValue));
	}

	@Override
	protected List<IHcThreadSpecificVar> createThreadSpecificVars(final ThreadInstance instance) {
		final var result = super.createThreadSpecificVars(instance);

		// add thread ID and sleep set
		result.add(0, new HcThreadIdVar(instance, mScript));
		result.add(1, new HcSleepVar(instance, mScript));

		return result;
	}

	@Override
	protected HornClauseBuilder buildInitialClause(final Map<ThreadInstance, IcfgLocation> initialLocations) {
		final var clause = super.buildInitialClause(initialLocations);

		// all sleep variables are initialized to 0
		for (final var instance : mInstances) {
			final var sleep = mSleepVars.get(instance);
			clause.addConstraint(SmtUtils.binaryEquality(mScript, clause.getHeadVar(sleep).getTerm(), numeral(0)));
		}

		return clause;
	}

	@Override
	protected HornClauseBuilder buildInductivityClause(final IIcfgTransition<?> transition,
			final Map<ThreadInstance, IcfgLocation> preds, final Map<ThreadInstance, IcfgLocation> succs,
			final ThreadInstance updatedThread) {
		final var clause = super.buildInductivityClause(transition, preds, succs, updatedThread);

		// active threads are not sleeping
		for (final var active : preds.keySet()) {
			final var sleep = mSleepVars.get(active);
			clause.addConstraint(SmtUtils.binaryEquality(mScript, clause.getBodyVar(sleep).getTerm(), numeral(0)));
		}

		// thread IDs are ordered
		ensureThreadOrdering(clause);

		// update sleep variables
		for (final var instance : mInstances) {
			updateSleepInductive(clause, transition, preds.keySet(), updatedThread, instance);
		}

		return clause;
	}

	@Override
	protected HornClauseBuilder buildNonInterferenceClause(final IIcfgTransition<?> transition) {
		final var clause = super.buildNonInterferenceClause(transition);

		final var interferingThread = getInterferingThread(transition);
		final var interferingId = new HcThreadIdVar(interferingThread, mScript);

		// thread IDs are ordered
		ensureThreadOrdering(clause);

		// ensure interfering thread has distinct thread ID
		for (final var instance : mInstances) {
			clause.addConstraint(SmtUtils.distinct(mScript, clause.getBodyVar(mIdVars.get(instance)).getTerm(),
					clause.getBodyVar(interferingId).getTerm()));
		}

		// interfering thread is not sleeping
		final var sleep = new HcSleepVar(interferingThread, mScript);
		clause.addConstraint(SmtUtils.binaryEquality(mScript, clause.getBodyVar(sleep).getTerm(), numeral(0)));

		// update sleep variables
		for (final var instance : mInstances) {
			updateSleepNonInterference(clause, transition, interferingId, instance);
		}

		return clause;
	}

	private void ensureThreadOrdering(final HornClauseBuilder clause) {
		for (int i = 0; i < mInstances.size(); ++i) {
			final var instance = mInstances.get(i);
			final var id = mIdVars.get(instance);

			// fix ordering between thread IDs
			if (i + 1 < mInstances.size()) {
				final var next = mInstances.get(i + 1);
				final var nextId = mIdVars.get(next);
				clause.addConstraint(
						SmtUtils.less(mScript, clause.getBodyVar(id).getTerm(), clause.getBodyVar(nextId).getTerm()));
			}
		}
	}

	// update sleep variable depending on commutativity and thread ID ordering
	// Here the ordering can be resolved statically
	private void updateSleepInductive(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final Set<ThreadInstance> activeThreads, final ThreadInstance primaryActiveThread,
			final ThreadInstance current) {
		final var loc = clause.getBodyVar(mLocationVars.get(current));
		final Term nonCommConstr = getNonCommutativityConstraint(current, loc.getTerm(), transition);

		// for now, the preference order is non-positional, and given by the ordering in mInstances
		final int ordering = Integer.compare(mInstances.indexOf(primaryActiveThread), mInstances.indexOf(current));

		final var sleep = mSleepVars.get(current);
		if (activeThreads.contains(current)) {
			// no update of sleep variable
		} else if (ordering < 0) {
			// set sleep variable to false / leave unchanged
			clause.differentBodyHeadVar(sleep);
			final var oldSleep = clause.getBodyVar(sleep);
			final var newSleep = clause.getHeadVar(sleep);
			clause.addConstraint(SmtUtils.ite(mScript, nonCommConstr,
					SmtUtils.binaryEquality(mScript, newSleep.getTerm(), numeral(0)),
					SmtUtils.binaryEquality(mScript, newSleep.getTerm(), oldSleep.getTerm())));
		} else {
			// set sleep variable to false / true
			clause.differentBodyHeadVar(sleep);
			final var newSleep = clause.getHeadVar(sleep);
			clause.addConstraint(SmtUtils.binaryBooleanEquality(mScript,
					SmtUtils.binaryEquality(mScript, newSleep.getTerm(), numeral(0)), nonCommConstr));
		}
	}

	// update sleep variable depending on commutativity and thread ID ordering
	// Here the ordering can only be resolved at runtime, so we treat it statically
	private void updateSleepNonInterference(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final HcThreadIdVar interferingId, final ThreadInstance current) {
		final var sleep = mSleepVars.get(current);
		clause.differentBodyHeadVar(sleep);
		final var oldSleep = clause.getBodyVar(sleep);
		final var newSleep = clause.getHeadVar(sleep);

		final var currentLoc = clause.getBodyVar(mLocationVars.get(current));
		final var currentId = clause.getBodyVar(mIdVars.get(current));

		final Term nonCommConstr = getNonCommutativityConstraint(current, currentLoc.getTerm(), transition);
		clause.addConstraint(SmtUtils.binaryBooleanEquality(mScript,
				SmtUtils.binaryEquality(mScript, newSleep.getTerm(), numeral(0)),
				SmtUtils.or(mScript,
						SmtUtils.and(mScript,
								SmtUtils.greater(mScript, currentId.getTerm(),
										clause.getBodyVar(interferingId).getTerm()),
								SmtUtils.binaryEquality(mScript, oldSleep.getTerm(), numeral(0))),
						nonCommConstr)));
	}

	protected Term getNonCommutativityConstraint(final ThreadInstance instance, final Term locVar,
			final IIcfgTransition<?> currentEdge) {

		final var nonCommLocations = new HashSet<Term>();
		for (final var loc : mThreadLocations.get(instance.getTemplateName())) {
			if (loc.getOutgoingEdges().stream()
					.anyMatch(edge -> mIndependence.isIndependent(null, edge, currentEdge) != Dependence.INDEPENDENT)) {
				nonCommLocations.add(getLocIndexTerm(loc, instance.getTemplateName()));
			}
		}
		return SmtUtils.or(mScript, nonCommLocations.stream().map(loc -> SmtUtils.binaryEquality(mScript, locVar, loc))
				.collect(Collectors.toList()));
	}
}
