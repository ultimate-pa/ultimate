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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Iterated symbolic memory of a loop.
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public class IteratedSymbolicMemory {

	private final IUltimateServiceProvider mServices;
	private final Map<IProgramVar, Term> mIteratedMemory;
	private final Map<IProgramVar, Term> mMemoryMapping;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final Loop mLoop;
	private final List<TermVariable> mPathCounters;
	private final Map<TermVariable, TermVariable> mNewPathCounters;
	private final ManagedScript mScript;
	private final ILogger mLogger;
	private Term mAbstractPathCondition;
	private UnmodifiableTransFormula mAbstractFormula;

	private enum mCaseType {
		NOT_CHANGED, ADDITION, SUBTRACTION, CONSTANT_ASSIGNMENT, CONSTANT_ASSIGNMENT_PATHCOUNTER
	}

	/**
	 * Construct new Iterated symbolic memory of a loop
	 *
	 * @param script
	 *            a {@link ManagedScript}
	 * @param logger
	 *            a {@link ILogger}
	 * @param tf
	 * @param oldSymbolTable
	 * @param loop
	 *            {@link Loop} whose iterated memory is computed
	 * @param pathCounters
	 *            list of pathcounters of the loops backbones
	 * @param newPathCounter
	 *            mapping of {@link TermVariable} to new Path Counter Tau
	 */
	public IteratedSymbolicMemory(final ManagedScript script, final IUltimateServiceProvider services,
			final ILogger logger, final Loop loop, final List<TermVariable> pathCounters,
			final Map<TermVariable, TermVariable> newPathCounter) {

		mServices = services;
		mLogger = logger;
		mIteratedMemory = new HashMap<>();
		mPathCounters = pathCounters;
		mNewPathCounters = newPathCounter;
		mScript = script;
		mAbstractPathCondition = mScript.getScript().term("true");
		mLoop = loop;
		mInVars = mLoop.getInVars();
		mOutVars = mLoop.getOutVars();

		mAbstractFormula = null;

		mMemoryMapping = new HashMap<>();

		for (final Entry<IProgramVar, TermVariable> entry : mInVars.entrySet()) {
			mMemoryMapping.put(entry.getKey(), (TermVariable) entry.getValue());
		}

		for (final Entry<IProgramVar, TermVariable> entry : mOutVars.entrySet()) {
			if (!mMemoryMapping.containsKey(entry.getKey())) {
				mMemoryMapping.put(entry.getKey(), (TermVariable) entry.getValue());
			}
		}

		for (final Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {
			mIteratedMemory.put(entry.getKey(), null);
		}
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
					mLogger.debug("None of the cases applicable " + entry.getKey() + " value = unknown");
					break;
				}

				final Term memory = backbone.getSymbolicMemory().getValue(entry.getKey());

				// Case 1: variable not changed in backbone
				if (memory == null || memory.equals(symbol) || memory instanceof TermVariable) {
					continue;
				}

				// Case 3:
				// in each backbone the variable is either not changed or set to
				// an expression,
				if (memory instanceof ConstantTerm) {

					update = memory;
					prevCase = caseType;
					caseType = mCaseType.CONSTANT_ASSIGNMENT;

					mLogger.debug("Assignment");
				} else {

					// Case 2.1: if the variable is changed from its symbol by
					// adding
					// a constant for each backbone.
					if ("+".equals(((ApplicationTerm) memory).getFunction().getName())) {

						mLogger.debug("Addition");

						update = mScript.getScript().term("+", update, mScript.getScript().term("*",
								((ApplicationTerm) memory).getParameters()[1], backbone.getPathCounter()));

						prevCase = caseType;
						caseType = mCaseType.ADDITION;

					}

					// Case 2.2: if the variable is changed from its symbol by
					// subtracting
					// a constant for each backbone.
					if ("-".equals(((ApplicationTerm) memory).getFunction().getName())) {

						mLogger.debug("Subtraction");

						update = mScript.getScript().term("-", update, mScript.getScript().term("*",
								((ApplicationTerm) memory).getParameters()[1], backbone.getPathCounter()));

						prevCase = caseType;
						caseType = mCaseType.SUBTRACTION;

					}

					if (!Arrays.asList(((ApplicationTerm) memory).getParameters()).contains(symbol) && Arrays
							.asList(((ApplicationTerm) memory).getParameters()).contains(backbone.getPathCounter())) {

						final Map<Term, Term> mapping = new HashMap<>();

						final Term newMapping = mScript.getScript().term("-", backbone.getPathCounter(),
								Rational.ONE.toTerm(SmtSortUtils.getIntSort(mScript)));
						mapping.put(backbone.getPathCounter(), newMapping);

						final Substitution sub = new Substitution(mScript, mapping);
						update = sub.transform(memory);
					}
				}
			}

			mIteratedMemory.replace(entry.getKey(), update);
		}
	}

	/**
	 * Compute the abstract condition using the {@link IteratedSymbolicMemory}
	 */
	public void updateCondition() {

		for (final Backbone backbone : mLoop.getBackbones()) {

			final List<TermVariable> freeVars = new ArrayList<>();

			final UnmodifiableTransFormula backboneTf = (UnmodifiableTransFormula) mLoop
					.updateVars(backbone.getCondition(), mLoop.getInVars(), mLoop.getOutVars());
			Term condition = backboneTf.getFormula();

			for (final TermVariable var : condition.getFreeVars()) {
				if (mPathCounters.contains(var)) {
					freeVars.add(var);
				}
			}

			if (condition instanceof QuantifiedFormula) {
				condition = ((QuantifiedFormula) condition).getSubformula();
			}

			final Map<Term, Term> mapping = new HashMap<>();

			final ApplicationTerm appTerm = (ApplicationTerm) condition;

			for (Term term : appTerm.getParameters()) {
				mapping.putAll(termUnravel(term));
			}

			Substitution sub = new Substitution(mScript, mapping);
			Term newCondition = sub.transform(appTerm);
			mapping.clear();

			mapping.put(backbone.getPathCounter(), mNewPathCounters.get(backbone.getPathCounter()));

			sub = new Substitution(mScript, mapping);
			newCondition = sub.transform(newCondition);

			final List<TermVariable> tempPathCounters = new ArrayList<>(mPathCounters);
			tempPathCounters.remove(backbone.getPathCounter());

			final List<TermVariable> tempNewPathCounters = new ArrayList<>(mNewPathCounters.values());
			tempNewPathCounters.remove(mNewPathCounters.get(backbone.getPathCounter()));

			final Term t1 = mScript.getScript().term("<", mNewPathCounters.get(backbone.getPathCounter()),
					backbone.getPathCounter());
			final Term t2 = mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)),
					mNewPathCounters.get(backbone.getPathCounter()));

			Term tFirstPart = mScript.getScript().term("and", t1, t2);

			Term tBackPart = mScript.getScript().term("true");

			for (TermVariable var : tempPathCounters) {
				tBackPart = mScript.getScript().term("and", tBackPart, mScript.getScript().term("<=",
						Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)), mNewPathCounters.get(var), var));
			}

			Term tBackPartAddition = mScript.getScript().term("true");
			for (TermVariable var : freeVars) {
				tBackPartAddition = mScript.getScript().term("and", tBackPartAddition,
						mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)), var));
			}

			tBackPart = SmtUtils.and(mScript.getScript(), tBackPartAddition, newCondition);

			if (!freeVars.isEmpty()) {
				tBackPartAddition = mScript.getScript().quantifier(QuantifiedFormula.EXISTS,
						freeVars.toArray(new TermVariable[freeVars.size()]), tBackPartAddition);
			}

			tBackPart = SmtUtils.and(mScript.getScript(), tBackPart, tBackPartAddition);

			if (!tempNewPathCounters.isEmpty()) {
				tBackPart = mScript.getScript().quantifier(QuantifiedFormula.EXISTS,
						tempNewPathCounters.toArray(new TermVariable[tempNewPathCounters.size()]), tBackPart);
			}

			tFirstPart = Util.implies(mScript.getScript(), tFirstPart, tBackPart);

			final TermVariable[] vars = { mNewPathCounters.get(backbone.getPathCounter()) };
			final Term necessaryCondition = mScript.getScript().quantifier(QuantifiedFormula.FORALL, vars, tFirstPart);

			mAbstractPathCondition = SmtUtils.and(mScript.getScript(),
					Arrays.asList(mAbstractPathCondition, necessaryCondition));

			mAbstractPathCondition = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript,
					mAbstractPathCondition, SimplificationTechnique.SIMPLIFY_DDA,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

			Term newTerm = updateBackboneTerm(backbone);

			for (final TermVariable pathCounter : mPathCounters) {
				final Term t = mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)), pathCounter);
				newTerm = mScript.getScript().term("and", t, newTerm);
			}

			newTerm = mScript.getScript().quantifier(QuantifiedFormula.EXISTS,
					mPathCounters.toArray(new TermVariable[mPathCounters.size()]), newTerm);

			final Term simplifiedAbstractPathCondition = PartialQuantifierElimination.tryToEliminate(mServices, mLogger,
					mScript, newTerm, SimplificationTechnique.NONE,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

			backbone.setAbstractPathCondition(simplifiedAbstractPathCondition);
			mAbstractPathCondition = SmtUtils.or(mScript.getScript(), mAbstractPathCondition,
					simplifiedAbstractPathCondition);

		}

		for (final TermVariable kappa : mPathCounters) {
			mAbstractPathCondition = mScript.getScript().term("and", mAbstractPathCondition,
					mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)), kappa));
		}

		final TransFormulaBuilder tfb = new TransFormulaBuilder(mInVars, mOutVars, true, null, true, null, false);

		mAbstractPathCondition = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript,
				mAbstractPathCondition, SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		for (final Entry<IProgramVar, TermVariable> outvar : mOutVars.entrySet()) {
			mAbstractPathCondition = mScript.getScript().term("and", mAbstractPathCondition,
					mScript.getScript().term("=", outvar.getValue(), mIteratedMemory.get(outvar.getKey())));
		}

		tfb.setFormula(mAbstractPathCondition);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);

		tfb.addAuxVarsButRenameToFreshCopies(mNewPathCounters.keySet(), mScript);
		final Set<TermVariable> values = new HashSet<>(mNewPathCounters.values());

		tfb.addAuxVarsButRenameToFreshCopies(values, mScript);

		mAbstractFormula = tfb.finishConstruction(mScript);

		mLogger.debug("ITERATEDSYMBOLIC MEMORY: " + mAbstractPathCondition);
	}

	/**
	 * update the backbones {@link TransFormula} with the new iterated values.
	 * 
	 * @param backbone
	 *            the backbone to be updated
	 * @return term with updated values
	 */
	public Term updateBackboneTerm(final Backbone backbone) {
		Term condition = backbone.getFormula().getFormula();
		final Map<Term, Term> subMapping = termUnravel(condition);
		final Substitution sub = new Substitution(mScript, subMapping);
		return sub.transform(condition);
	}

	private Map<Term, Term> termUnravel(Term term) {
		final Map<Term, Term> result = new HashMap<>();
		if (term instanceof QuantifiedFormula) {
			return result;
		}

		if (term instanceof TermVariable) {
			final TermVariable tv = (TermVariable) term;
			for (Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {

				if (tv.equals(entry.getValue()) && !(mIteratedMemory.get(entry.getKey()) instanceof ConstantTerm)) {
					result.put(term, mIteratedMemory.get(entry.getKey()));
					break;
				}
			}
			return result;
		}

		if (term instanceof ConstantTerm) {
			return result;
		}
		final ApplicationTerm appTerm = (ApplicationTerm) term;
		for (Term subTerm : appTerm.getParameters()) {
			result.putAll(termUnravel(subTerm));
		}
		return result;
	}

	/**
	 * update the backbones {@link TransFormula} with the new iterated values.
	 * 
	 * @param tf
	 *            the transformula to be updated
	 * @return term with updated values
	 */
	public Term updateBackboneTerm(final TransFormula tf) {
		Term condition = tf.getFormula();
		final Map<Term, Term> subMapping = termUnravel(condition);
		final Substitution sub = new Substitution(mScript, subMapping);
		return sub.transform(condition);
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

	public Term getAbstractCondition() {
		return mAbstractPathCondition;
	}

	public UnmodifiableTransFormula getAbstractFormula() {
		return mAbstractFormula;
	}
}
