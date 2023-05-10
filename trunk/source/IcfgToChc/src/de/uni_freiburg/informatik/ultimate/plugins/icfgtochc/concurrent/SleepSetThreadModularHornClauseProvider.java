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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.preferences.IcfgToChcPreferences;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetThreadModularHornClauseProvider extends ThreadModularHornClauseProvider {
	private final IIndependenceRelation<?, ? super IIcfgTransition<?>> mIndependence;
	private final Map<String, Collection<IcfgLocation>> mThreadLocations;

	private final Map<ThreadInstance, HcThreadIdVar> mIdVars;
	private final Map<ThreadInstance, HcSleepVar> mSleepVars;

	public SleepSetThreadModularHornClauseProvider(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final IIcfg<IcfgLocation> icfg, final HcSymbolTable symbolTable,
			final IIndependenceRelation<?, ? super IIcfgTransition<?>> independence, final IcfgToChcPreferences prefs) {
		super(services, mgdScript, icfg, symbolTable, prefs);
		mIndependence = independence;
		mThreadLocations = icfg.getProgramPoints().entrySet().stream()
				.collect(Collectors.toMap(Map.Entry::getKey, e -> e.getValue().values()));

		if (!mPrefs.breakPreferenceOrderSymmetry()) {
			mIdVars = extractThreadVars(HcThreadIdVar.class);
		} else {
			mIdVars = null;
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
		if (!mPrefs.breakPreferenceOrderSymmetry()) {
			ensureUniqueThreadIDs(clause);
		}

		// all sleep variables are initialized to false
		for (final var instance : mInstances) {
			final var sleep = mSleepVars.get(instance);
			clause.addConstraint(SmtUtils.not(mScript, clause.getHeadVar(sleep).getTerm()));
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
			clause.addConstraint(SmtUtils.not(mScript, clause.getBodyVar(sleep).getTerm()));
		}

		// update sleep variables
		for (final var instance : mInstances) {
			updateSleepInductive(clause, transition, preds.keySet(), updatedThread, instance);
		}

		return clause;
	}

	@Override
	protected List<HornClauseBuilder> buildNonInterferenceClauses(final IIcfgTransition<?> transition) {
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
	protected HornClauseBuilder buildNonInterferenceClause(final IIcfgTransition<?> transition) {
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
		for (final var instance : mInstances) {
			updateSleepNonInterference(clause, transition, interferingId, instance);
		}

		return clause;
	}

	// This overload constructs non-interference clauses where preference order symmetry is broken, and the preference
	// order is resolved statically.
	protected HornClauseBuilder buildNonInterferenceClause(final IIcfgTransition<?> transition, final int index) {
		if (!mPrefs.breakPreferenceOrderSymmetry()) {
			throw new UnsupportedOperationException("This method breaks preference order symmetry, which is turned off."
					+ " Call the other overload of this method instead.");
		}

		// TODO support transitions with multiple predecessors (joins)
		final var interferingThread = getInterferingThread(transition);
		// final var interferingVars = createThreadSpecificVars(interferingThread);
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
		for (final var instance : mInstances) {
			final var prefOrder = index < instance.getInstanceNumber() ? mScript.term(SMTLIBConstants.FALSE)
					: mScript.term(SMTLIBConstants.TRUE);
			updateSleep(clause, transition, instance, prefOrder);
		}

		return clause;
	}

	private void ensureUniqueThreadIDs(final HornClauseBuilder clause) {
		for (final var first : mInstances) {
			final var firstId = clause.getHeadVar(mIdVars.get(first));
			for (final var second : mInstances) {
				if (!Objects.equals(first, second)) {
					final var secondId = clause.getHeadVar(mIdVars.get(second));
					clause.addConstraint(SmtUtils.distinct(mScript, firstId.getTerm(), secondId.getTerm()));
				}
			}
		}
	}

	// update sleep variable depending on commutativity and preference order
	private void updateSleepInductive(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final Set<ThreadInstance> activeThreads, final ThreadInstance primaryActiveThread,
			final ThreadInstance current) {
		if (activeThreads.contains(current)) {
			// no update of sleep variable
			return;
		}

		final Term prefOrder;
		if (mPrefs.breakPreferenceOrderSymmetry()) {
			// We resolve the preference order statically.
			// For now, the preference order is non-positional, and given by the ordering in mInstances.
			final int ordering = Integer.compare(mInstances.indexOf(primaryActiveThread), mInstances.indexOf(current));
			// Formula expressing whether current thread is BEFORE primary thread.
			prefOrder = ordering < 0 ? mScript.term(SMTLIBConstants.FALSE) : mScript.term(SMTLIBConstants.TRUE);
		} else {
			// We resolve the preference order symbolically, using ID variables.
			prefOrder = symbolicPreferenceOrderConstraint(clause, current, primaryActiveThread);
		}

		updateSleep(clause, transition, current, prefOrder);
	}

	// update sleep variable depending on commutativity and preference order
	private void updateSleepNonInterference(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final HcThreadIdVar interferingId, final ThreadInstance current) {
		// TODO if breaking symmetry, do this statically!
		final var prefOrder = symbolicPreferenceOrderConstraint(clause, current, interferingId.getThreadInstance());

		updateSleep(clause, transition, current, prefOrder);
	}

	// update sleep variable depending on commutativity and preference order
	private void updateSleep(final HornClauseBuilder clause, final IIcfgTransition<?> transition,
			final ThreadInstance current, final Term prefOrder) {
		final var sleep = mSleepVars.get(current);
		clause.differentBodyHeadVar(sleep);

		final var oldSleep = clause.getBodyVar(sleep);
		final var newSleep = clause.getHeadVar(sleep);

		final var canBePutToSleep = SmtUtils.or(mScript, prefOrder, oldSleep.getTerm());

		if (SmtUtils.isFalseLiteral(canBePutToSleep)) {
			// optimization: If commutativity does not play a role, skip computation of commutativity constraint
			// sleep' = false
			clause.addConstraint(
					SmtUtils.binaryBooleanEquality(mScript, newSleep.getTerm(), mScript.term(SMTLIBConstants.FALSE)));
			return;
		}

		// get constraint describing commutativity
		final var currentLoc = clause.getBodyVar(mLocationVars.get(current));
		final Term commConstr = getCommutativityConstraint(current, currentLoc.getTerm(), transition);

		// sleep' = (current < interfering \/ sleep) /\ commConstr
		clause.addConstraint(SmtUtils.binaryBooleanEquality(mScript, newSleep.getTerm(),
				SmtUtils.and(mScript, canBePutToSleep, commConstr)));
	}

	private Term symbolicPreferenceOrderConstraint(final HornClauseBuilder clause, final ThreadInstance current,
			final ThreadInstance active) {
		final var currentId = clause.getBodyVar(new HcThreadIdVar(current, mScript));
		final var activeId = clause.getBodyVar(new HcThreadIdVar(active, mScript));
		return SmtUtils.less(mScript, currentId.getTerm(), activeId.getTerm());
	}

	protected Term getCommutativityConstraint(final ThreadInstance instance, final Term locVar,
			final IIcfgTransition<?> currentEdge) {
		final var commLocations = new HashSet<Term>();
		for (final var loc : mThreadLocations.get(instance.getTemplateName())) {
			// TODO can be optimized: if (= locVar loc) is false, don't check independence
			if (loc.getOutgoingEdges().stream()
					// ignore spec edges: the original edges are replaced, and the replacing transitions commute
					.filter(e -> !isPreConditionSpecEdge(e) && !isPostConditionSpecEdge(e))
					.allMatch(e -> mIndependence.isIndependent(null, e, currentEdge) == Dependence.INDEPENDENT)) {
				commLocations.add(getLocIndexTerm(loc, instance.getTemplateName()));
			}
		}
		return SmtUtils.or(mScript, commLocations.stream().map(loc -> SmtUtils.binaryEquality(mScript, locVar, loc))
				.collect(Collectors.toList()));
	}
}
