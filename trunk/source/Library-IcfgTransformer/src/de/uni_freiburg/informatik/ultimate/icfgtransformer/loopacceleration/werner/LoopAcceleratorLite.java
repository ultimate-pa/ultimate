/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Jonas Werner (jonaswerner95@gmail.com)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate.SimultaneousUpdateException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class LoopAcceleratorLite {

	private final List<TermVariable> mPathCounter;
	private final Map<TermVariable, TermVariable> mNewPathCounter;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IIcfgSymbolTable mOldSymbolTable;

	/**
	 * Version of symbolic iteration loop acceleration changed so that only the loop accelerations are returned. This
	 * version is not used in {@link WernerLoopAccelerationIcfgTransformer} to transform loops.
	 *
	 * @param pathCounter
	 * @param newPathCounter
	 * @param acceleratedLoops
	 * @param script
	 * @param services
	 * @param logger
	 * @param oldSymbolTable
	 */
	public LoopAcceleratorLite(final ManagedScript script, final IUltimateServiceProvider services,
			final ILogger logger, final IIcfgSymbolTable oldSymbolTable) {
		mNewPathCounter = new HashMap<>();
		mPathCounter = new ArrayList<>();
		mScript = script;
		mServices = services;
		mLogger = logger;
		mOldSymbolTable = oldSymbolTable;
	}

	/**
	 * Given a loop with its backbones construct a loop summary.
	 *
	 * @param loop
	 * @return
	 */
	public UnmodifiableTransFormula summarizeLoop(final Loop loop) {
		mPathCounter.clear();
		mNewPathCounter.clear();

		if (SmtUtils.isTrueLiteral(loop.getFormula().getFormula())
				|| SmtUtils.isFalseLiteral(loop.getFormula().getFormula())) {
			return null;
		}

		/**
		 * Go through each backbone and construct a symbolic memory.
		 */
		for (final Backbone backbone : loop.getBackbones()) {
			calculateSymbolicMemory(backbone, loop);
			if (backbone.getCondition() == null) {
				return null;
			}
		}

		for (int i = 0; i < mPathCounter.size(); i++) {
			final TermVariable newBackbonePathCounter =
					mScript.constructFreshTermVariable("tau", mScript.getScript().sort(SmtSortUtils.INT_SORT));
			mNewPathCounter.put(mPathCounter.get(i), newBackbonePathCounter);
		}
		loop.addVar(mPathCounter);
		final List<TermVariable> newPathCounterVals = new ArrayList<>(mNewPathCounter.values());
		loop.addVar(newPathCounterVals);

		final List<TermVariable> pathCounters = new ArrayList<>(mPathCounter);
		final IteratedSymbolicMemory iteratedSymbolicMemory =
				new IteratedSymbolicMemory(mScript, mServices, mLogger, loop, pathCounters, mNewPathCounter);

		/**
		 * get the iterated variable values.
		 */
		iteratedSymbolicMemory.updateMemory();
		iteratedSymbolicMemory.updateCondition();

		Term loopSummary = iteratedSymbolicMemory.getAbstractCondition();
		/**
		 * Dealing with nested loops by combining the two accelerated loop summaries.
		 */
		if (!loop.getNestedLoops().isEmpty()) {
			for (final Loop nestedLoop : loop.getNestedLoops()) {

				for (final UnmodifiableTransFormula exitTerm : nestedLoop.getExitConditions()) {
					loopSummary = SmtUtils.or(mScript.getScript(), Arrays.asList(loopSummary, exitTerm.getFormula()));
					final ArrayList<TermVariable> newAuxVars = new ArrayList<>(exitTerm.getAuxVars());
					loop.addVar(newAuxVars);

					loopSummary = loop.updateVars(loopSummary, exitTerm.getInVars(), exitTerm.getOutVars());
				}
				final Map<IProgramVar, TermVariable> oldOutVars = loop.getOutVars();

				for (final Entry<IProgramVar, TermVariable> outVarNested : nestedLoop.getOutVars().entrySet()) {
					if (!oldOutVars.containsKey(outVarNested.getKey())) {
						oldOutVars.put(outVarNested.getKey(), outVarNested.getValue());
					}
				}
			}
		}
		final Set<TermVariable> aux = new HashSet<>(loop.getVars());
		final UnmodifiableTransFormula exitFormula =
				buildFormula(mScript, loopSummary, loop.getInVars(), loop.getOutVars(), aux);
		return exitFormula;

	}

	/**
	 * Execute backbone once to get a symbolic memory.
	 *
	 * @param backbone
	 * @param loop
	 */
	private void calculateSymbolicMemory(final Backbone backbone, final Loop loop) {
		final SimultaneousUpdate update;
		try {
			update = SimultaneousUpdate.fromTransFormula(mServices, backbone.getFormula(), mScript);
		} catch (final SimultaneousUpdateException e) {
			throw new IllegalArgumentException(e.getMessage());
		}
		final Set<TermVariable> aux = new HashSet<>(loop.getVars());
		final TransFormula tf = buildFormula(mScript, loop.updateVars(backbone.getFormula().getFormula(),
				backbone.getFormula().getInVars(), backbone.getFormula().getOutVars()), loop.getInVars(),
				loop.getOutVars(), aux);

		backbone.setFormula(tf);

		final SymbolicMemory symbolicMemory = new SymbolicMemory(mScript, mServices, tf, mOldSymbolTable);
		symbolicMemory.updateVars(update.getDeterministicAssignment());

		final UnmodifiableTransFormula condition = symbolicMemory.updateCondition(
				TransFormulaUtils.computeGuard((UnmodifiableTransFormula) tf, mScript, mServices));

		final TermVariable backbonePathCounter =
				mScript.constructFreshTermVariable("kappa", mScript.getScript().sort(SmtSortUtils.INT_SORT));

		mPathCounter.add(backbonePathCounter);
		backbone.setPathCounter(backbonePathCounter);
		backbone.setCondition(condition);
		backbone.setSymbolicMemory(symbolicMemory);
	}

	/**
	 * return a {@link UnmodifiableTransFormula} of the given term.
	 *
	 * @param script
	 *            {@link ManagedScript}
	 * @param term
	 *            term for the new Transformula
	 * @param inVars
	 *            map of invars
	 * @param outVars
	 *            map of outvars
	 * @param auxVars
	 *            set of auxvars
	 * @return a constructed {@link UnmodifiableTransFormula}
	 */
	public static UnmodifiableTransFormula buildFormula(final ManagedScript script, final Term term,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars,
			final Set<TermVariable> auxVars) {
		final Boolean emptyAux = auxVars.isEmpty();
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true, null, true, null, emptyAux);
		tfb.setFormula(term);
		tfb.addAuxVarsButRenameToFreshCopies(auxVars, script);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(script);
	}

}
