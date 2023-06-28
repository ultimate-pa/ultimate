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
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.HcLocationVar;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.HornClauseBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IHcThreadSpecificVar;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ThreadInstance;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ThreadModularHornClauseProvider;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences.IcfgToChcPreferences;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetThreadModularHornClauseProvider extends ThreadModularHornClauseProvider {
	private final IndependenceChecker mIndependenceChecker;
	private final IPreferenceOrderManager mPreferenceManager;
	private final Map<String, Collection<IcfgLocation>> mThreadLocations;

	private final Map<ThreadInstance, HcThreadIdVar> mIdVars;
	private final Map<ThreadInstance, HcSleepVar> mSleepVars;

	public SleepSetThreadModularHornClauseProvider(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final IIcfg<IcfgLocation> icfg, final HcSymbolTable symbolTable,
			final ISymbolicIndependenceRelation<? super IIcfgTransition<?>> independence,
			final IThreadModularPreferenceOrder preferenceOrder, final IcfgToChcPreferences prefs) {
		super(services, mgdScript, icfg, symbolTable, prefs);
		mIndependenceChecker = new IndependenceChecker(services, icfg.getCfgSmtToolkit(), independence);
		mThreadLocations = icfg.getProgramPoints().entrySet().stream().collect(Collectors.toMap(Map.Entry::getKey,
				e -> e.getValue().values().stream().filter(this::isRelevantLocation).collect(Collectors.toList())));

		if (mPrefs.breakPreferenceOrderSymmetry()) {
			mIdVars = null;
			mPreferenceManager = new ExplicitPreferenceOrderManager(preferenceOrder, mScript, mLocationIndices);
		} else {
			mIdVars = extractThreadVars(HcThreadIdVar.class);
			mPreferenceManager = new SymbolicPreferenceOrderManager(preferenceOrder, mScript, mLocationIndices);
		}
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

		// add sleep set variable
		result.add(0, new HcSleepVar(instance, mScript));

		if (!mPrefs.breakPreferenceOrderSymmetry()) {
			// add thread ID (used to describe preference order)
			result.add(0, new HcThreadIdVar(instance, mScript));
		}

		return result;
	}

	@Override
	protected HornClauseBuilder buildInitialClause() {
		final var clause = super.buildInitialClause();

		// thread IDs are pairwise different
		mPreferenceManager.ensureUniqueThreadIDs(clause, mInstances);

		// all sleep variables are initialized to false
		for (final var instance : mInstances) {
			final var sleep = mSleepVars.get(instance);
			clause.addConstraint(SmtUtils.not(mScript, clause.getHeadVar(sleep).getTerm()));
		}

		return clause;
	}

	@Override
	protected HornClauseBuilder buildInductivityClause(final IcfgEdge transition,
			final Map<ThreadInstance, IcfgLocation> preds, final Map<ThreadInstance, IcfgLocation> succs,
			final ThreadInstance updatedThread) {
		final var clause = super.buildInductivityClause(transition, preds, succs, updatedThread);

		// active threads are not sleeping
		for (final var active : preds.keySet()) {
			final var sleep = mSleepVars.get(active);
			clause.addConstraint(SmtUtils.not(mScript, clause.getBodyVar(sleep).getTerm()));
		}

		// update sleep variables
		for (final var instance : mInstances) {
			if (preds.containsKey(instance)) {
				// no update of sleep variable
				continue;
			}
			updateSleep(clause, updatedThread, transition, instance, Comparator.naturalOrder());
		}

		return clause;
	}

	@Override
	protected List<HornClauseBuilder> buildNonInterferenceClauses(final IcfgEdge transition) {
		if (!mPrefs.breakPreferenceOrderSymmetry()) {
			return super.buildNonInterferenceClauses(transition);
		}

		final var result = new ArrayList<HornClauseBuilder>();
		final var instanceCount = getInstances(transition.getPrecedingProcedure()).size();
		for (int i = 0; i <= instanceCount; ++i) {
			result.add(buildNonInterferenceClause(transition, i));
		}

		return result;
	}

	// This overload constructs non-interference clauses where the preference order is treated symbolically.
	@Override
	protected HornClauseBuilder buildNonInterferenceClause(final IcfgEdge transition) {
		if (mPrefs.breakPreferenceOrderSymmetry()) {
			throw new UnsupportedOperationException("This method does not support breaking preference order symmetry. "
					+ "Call the other overload of this method instead.");
		}

		final var clause = super.buildNonInterferenceClause(transition);

		final var interferingThread = getInterferingThread(transition);
		final var interferingId = new HcThreadIdVar(interferingThread, mScript);

		// ensure interfering thread has distinct thread ID
		for (final var instance : mInstances) {
			clause.addConstraint(SmtUtils.distinct(mScript, clause.getBodyVar(mIdVars.get(instance)).getTerm(),
					clause.getBodyVar(interferingId).getTerm()));
		}

		// interfering thread is not sleeping
		final var sleep = new HcSleepVar(interferingThread, mScript);
		clause.addConstraint(SmtUtils.not(mScript, clause.getBodyVar(sleep).getTerm()));

		// update sleep variables
		for (final var sleepingThread : mInstances) {
			updateSleep(clause, interferingThread, transition, sleepingThread, null);
		}

		return clause;
	}

	// This overload constructs non-interference clauses where preference order symmetry is broken, and the preference
	// order is resolved statically.
	protected HornClauseBuilder buildNonInterferenceClause(final IcfgEdge transition, final int index) {
		if (!mPrefs.breakPreferenceOrderSymmetry()) {
			throw new UnsupportedOperationException("This method breaks preference order symmetry, which is turned off."
					+ " Call the other overload of this method instead.");
		}

		// TODO support transitions with multiple predecessors (joins)
		final var interferingThread = getInterferingThread(transition);
		final var instances = getInstances(interferingThread.getTemplateName());

		final var clause = buildNonInterferenceClause(transition, (c, replacedInstance) -> {
			// the sequence of instances to consider
			final var relevantInstances = new ArrayList<>(instances);
			relevantInstances.add(index, interferingThread);
			relevantInstances.remove(replacedInstance);

			final var substitution = IntStream.range(0, instances.size())
					.mapToObj(i -> new Pair<>(instances.get(i), relevantInstances.get(i)))
					.collect(Collectors.toMap(Pair::getKey, Pair::getValue));

			// take the default parameters, and adjust them to the relevant sequence of instances
			final var bodyArgs = new ArrayList<>(mInvariantPredicate.getParameters());
			for (int i = 0; i < bodyArgs.size(); ++i) {
				final var arg = bodyArgs.get(i);
				if (!(arg instanceof IHcThreadSpecificVar)) {
					continue;
				}
				final var specific = (IHcThreadSpecificVar) arg;
				final var oldThread = specific.getThreadInstance();
				final var newThread = substitution.get(oldThread);
				if (newThread != null) {
					assert Objects.equals(oldThread.getTemplateName(), newThread.getTemplateName());
					final var replaced = specific.forInstance(newThread.getInstanceNumber());
					bodyArgs.set(i, replaced);
				}
			}

			return bodyArgs.stream().map(v -> c.getBodyVar(v).getTerm()).collect(Collectors.toList());
		});

		// interfering thread is not sleeping
		final var sleep = new HcSleepVar(interferingThread, mScript);
		clause.addConstraint(SmtUtils.not(mScript, clause.getBodyVar(sleep).getTerm()));

		// update sleep variables
		for (final var sleepingThread : mInstances) {
			updateSleep(clause, interferingThread, transition, sleepingThread,
					ThreadInstance.getNonInterferenceComparator(index));
		}

		return clause;
	}

	// update sleep variable depending on commutativity and preference order
	private void updateSleep(final HornClauseBuilder clause, final ThreadInstance activeThread,
			final IcfgEdge activeEdge, final ThreadInstance updatedThread,
			final Comparator<ThreadInstance> comparator) {
		// The sleep variable of updatedThread is modified.
		final var sleep = mSleepVars.get(updatedThread);
		clause.differentBodyHeadVar(sleep);
		final var oldSleep = clause.getBodyVar(sleep);
		final var newSleep = clause.getHeadVar(sleep);

		// Determine the preference order constraint, expressing that updatedThread is preferable to activeThread.
		// updatedThread < activeThread
		final var updatedLocTerm = clause.getBodyVar(new HcLocationVar(updatedThread, mScript)).getTerm();
		final var activeLoc = activeEdge.getSource();
		final var activeLocTerm = getLocIndexTerm(activeLoc);
		final var prefOrder = mPreferenceManager.getOrderConstraint(clause, comparator, updatedThread, null,
				updatedLocTerm, activeThread, activeLoc, activeLocTerm);

		// Determine if updatedThread can be put to sleep (or continue to sleep).
		// (updatedThread < activeThread) \/ sleep
		final var canBePutToSleep = SmtUtils.or(mScript, prefOrder, oldSleep.getTerm());

		if (SmtUtils.isFalseLiteral(canBePutToSleep)) {
			// Optimization: If commutativity does not play a role, skip computation of commutativity constraint.
			// sleep' = false
			clause.addConstraint(
					SmtUtils.binaryBooleanEquality(mScript, newSleep.getTerm(), mScript.term(SMTLIBConstants.FALSE)));
			return;
		}

		// Get constraint describing commutativity.
		final var currentLoc = clause.getBodyVar(mLocationVars.get(updatedThread));
		final Term commConstr =
				getCommutativityConstraint(clause, activeThread, activeEdge, updatedThread, currentLoc.getTerm());

		// Update the sleep variable of updatedThread, according to the sleep set rule.
		// sleep' = ((updatedThread < activeThread) \/ sleep) /\ commConstr
		clause.addConstraint(SmtUtils.binaryBooleanEquality(mScript, newSleep.getTerm(),
				SmtUtils.and(mScript, canBePutToSleep, commConstr)));
	}

	protected Term getCommutativityConstraint(final HornClauseBuilder clause, final ThreadInstance activeThread,
			final IcfgEdge activeEdge, final ThreadInstance otherThread, final Term otherLocVar) {
		final var disjuncts = new ArrayList<Term>();
		for (final var loc : mThreadLocations.get(otherThread.getTemplateName())) {
			final var locEquality = SmtUtils.binaryEquality(mScript, otherLocVar, getLocIndexTerm(loc));
			if (SmtUtils.isFalseLiteral(locEquality)) {
				continue;
			}

			final var commConstraint = getCommutativityConstraint(clause, activeThread, activeEdge, otherThread, loc);
			if (SmtUtils.isFalseLiteral(commConstraint)) {
				continue;
			}

			final var disjunct = SmtUtils.and(mScript, locEquality, commConstraint);
			if (SmtUtils.isTrueLiteral(disjunct)) {
				// escape early if commutativity is guaranteed
				return mScript.term(SMTLIBConstants.TRUE);
			}

			disjuncts.add(disjunct);
		}
		return SmtUtils.or(mScript, disjuncts);
	}

	protected Term getCommutativityConstraint(final HornClauseBuilder clause, final ThreadInstance activeThread,
			final IcfgEdge activeEdge, final ThreadInstance otherThread, final IcfgLocation otherLoc) {
		final var conjuncts = new ArrayList<Term>();
		for (final var edge : otherLoc.getOutgoingEdges()) {
			if (isPreConditionSpecEdge(edge) || isPostConditionSpecEdge(edge)) {
				// ignore spec edges: the original edges are replaced, and the replacing edges commute with everything
				continue;
			}

			if (isSkippableAssertEdge(edge)) {
				// ignore assert edges if option is set
				continue;
			}

			final var conjunct =
					mIndependenceChecker.getIndependenceCondition(clause, activeThread, activeEdge, otherThread, edge);
			if (SmtUtils.isFalseLiteral(conjunct)) {
				// escape early if one outgoing edge does not commute under any circumstances
				return mScript.term(SMTLIBConstants.FALSE);
			}
			conjuncts.add(conjunct);
		}
		return SmtUtils.and(mScript, conjuncts);
	}
}
