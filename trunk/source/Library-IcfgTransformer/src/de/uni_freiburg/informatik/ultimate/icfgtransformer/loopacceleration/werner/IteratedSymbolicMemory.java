/*
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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Iterated symbolic memory of a loop.
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public class IteratedSymbolicMemory extends SymbolicMemory {

	private final Map<IProgramVar, Term> mIteratedMemory;
	private final Loop mLoop;
	private final List<TermVariable> mPathCounters;
	private final List<TermVariable> mNewPathCounters;
	private final IIcfgSymbolTable mOldsymbolTable;

	private enum mCaseType {
		NOT_CHANGED, ADDITION, CONSTANT_ASSIGNMENT, CONSTANT_ASSIGNMENT_PATHCOUNTER
	}

	/**
	 * Construct new Iterated symbolic memory of a loop
	 *
	 * @param script
	 * @param logger
	 * @param tf
	 * @param oldSymbolTable
	 * @param loop
	 *            {@link Loop} whose iterated memory is computed
	 * @param pathCounters
	 *            list of pathcounters of the loops backbones
	 */
	public IteratedSymbolicMemory(final ManagedScript script, final ILogger logger, final TransFormula tf,
			final IIcfgSymbolTable oldSymbolTable, final Loop loop, final List<TermVariable> pathCounters) {

		super(script, logger, tf, oldSymbolTable);
		mIteratedMemory = new HashMap<>();
		mPathCounters = pathCounters;
		mNewPathCounters = new ArrayList<>();
		mOldsymbolTable = oldSymbolTable;

		for (int i = 0; i < pathCounters.size(); i++) {
			final TermVariable newBackbonePathCounter = mScript.constructFreshTermVariable("tau",
					mScript.getScript().sort(SmtSortUtils.INT_SORT));
			mNewPathCounters.add(newBackbonePathCounter);
		}

		for (final Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {
			mIteratedMemory.put(entry.getKey(), null);
		}
		mLoop = loop;
		mLogger.debug("Iterated Memory: " + mIteratedMemory);
		// mLogger.debug("New PathCounters: " + mNewPathCounters);
	}

	/**
	 * update the iterated memory by using the symbolic memories of the
	 * backbones.
	 */
	public void updateMemory() {

		for (final Entry<IProgramVar, Term> entry : mIteratedMemory.entrySet()) {

			final Term symbol = mMemoryMapping.get(entry.getKey());

			Term update = symbol;
			mCaseType caseType = mCaseType.NOT_CHANGED;
			mCaseType prevCase = mCaseType.NOT_CHANGED;

			for (final Backbone backbone : mLoop.getBackbones()) {

				// A new value can only be computed, iff the cases do not
				// change.
				if (!caseType.equals(prevCase) && !prevCase.equals(mCaseType.NOT_CHANGED)) {
					update = null;
					mLogger.debug("None of the cases applicable " + entry.getKey() + " value = unknown!!");
					break;
				}

				final Term memory = backbone.getSymbolicMemory().getValue(entry.getKey());

				// Case 1: variable not changed in backbone
				if (memory == null) {
					continue;
				}

				mLogger.debug("Symbol: " + mMemoryMapping.get(entry.getKey()));
				mLogger.debug("BackMem: " + memory);

				// @Todo:
				if (memory instanceof TermVariable || memory instanceof ConstantTerm) {
					update = memory;
					continue;
				}

				// Case 2: if the variable is changed from its symbol by adding
				// a constant for each backbone.
				if (!memory.equals(symbol) && "+".equals(((ApplicationTerm) memory).getFunction().getName())
						&& Arrays.asList(((ApplicationTerm) memory).getParameters()).contains(symbol)) {

					mLogger.debug("Addition");

					update = mScript.getScript().term("+", update, mScript.getScript().term("*",
							((ApplicationTerm) memory).getParameters()[1], backbone.getPathCounter()));

					prevCase = caseType;
					caseType = mCaseType.ADDITION;

					mLogger.debug("Update: " + update);
				}

				// Case 3:
				// in each backbone the variable is either not changed or set to
				// an expression,
				if (!memory.equals(symbol)
						&& !Arrays.asList(((ApplicationTerm) memory).getParameters()).contains(symbol)) {

					update = memory;
					prevCase = caseType;
					caseType = mCaseType.CONSTANT_ASSIGNMENT;

					mLogger.debug("Assignment");
				}

				// TODO only allowed in one backbone
				if (!memory.equals(symbol)
						&& !Arrays.asList(((ApplicationTerm) memory).getParameters()).contains(symbol)
						&& Arrays.asList(((ApplicationTerm) memory).getParameters())
								.contains(backbone.getPathCounter())) {

					final Map<Term, Term> mapping = new HashMap<>();

					final Term newMapping = mScript.getScript().term("-", backbone.getPathCounter(),
							mScript.getScript().numeral("1"));
					mapping.put(backbone.getPathCounter(), newMapping);

					final Substitution sub = new Substitution(mScript, mapping);
					update = sub.transform(memory);
				}
			}
			mIteratedMemory.replace(entry.getKey(), update);
		}
		mLogger.debug("Iterated Memory: " + mIteratedMemory);
	}

	/**
	 * Compute the abstract condition using the {@link IteratedSymbolicMemory}
	 */
	public void updateCondition() {
		for (final Backbone backbone : mLoop.getBackbones()) {
			final List<TermVariable> freeVars = new ArrayList<>();
			for (final TermVariable var : backbone.getCondition().getFreeVars()) {
				if (mPathCounters.contains(var)) {
					freeVars.add(var);
				}
			}

			final Map<Term, Term> mapping = new HashMap<>();
			final ApplicationTerm appTerm = (ApplicationTerm) backbone.getCondition();
			for (Term term : appTerm.getParameters()) {
				mLogger.debug("Params: " + term);
				if (term instanceof TermVariable
						&& mIteratedMemory.containsKey(mOldsymbolTable.getProgramVar((TermVariable) term))) {
					mapping.put(term, mIteratedMemory.get(mOldsymbolTable.getProgramVar((TermVariable) term)));
					continue;
				}

				if (term instanceof ConstantTerm) {
					continue;
				}

				mapping.putAll(termUnravel((ApplicationTerm) term));

			}
			mLogger.debug("MAPPING: " + mapping);
		}
	}

	/**
	 * Get the iterated memory mapping
	 * 
	 * @return
	 */
	public Map<IProgramVar, Term> getIteratedMemory() {
		return mIteratedMemory;
	}

	/**
	 * Get the pathcounters of the {@link Backbone}s
	 * 
	 * @return
	 */
	public List<TermVariable> getPathCounters() {
		return mPathCounters;
	}
}
