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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
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
import de.uni_freiburg.informatik.ultimate.logic.Sort;
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
	private boolean mOverapprox;

	private final List<Term> mTerms;

	private final List<IProgramVar> mIllegal;

	private enum caseType {
		NOT_CHANGED, ADDITION, SUBTRACTION, MULTIPLICATION, CONSTANT_ASSIGNMENT, CONSTANT_ASSIGNMENT_PATHCOUNTER
	}

	/**
	 * Construct a new iterated symbolic memory for a loop.
	 *
	 * @param script
	 *            a {@link ManagedScript}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param logger
	 *            {@link ILogger}
	 * @param loop
	 *            the corresponding {@link Loop}
	 * @param pathCounters
	 *            a List of pathCounters
	 * @param newPathCounter
	 *            mapping of old pathcounters to new
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

		mOverapprox = false;
		mTerms = new ArrayList<>();

		mIllegal = new ArrayList<>();

		if (pathCounters.size() > 1) {
			mOverapprox = true;
		}

		mMemoryMapping = new HashMap<>();

		/**
		 * initialize the memory.
		 */
		for (final Entry<IProgramVar, TermVariable> entry : mInVars.entrySet()) {
			mMemoryMapping.put(entry.getKey(), entry.getValue());
		}

		for (final Entry<IProgramVar, TermVariable> entry : mOutVars.entrySet()) {
			if (!mMemoryMapping.containsKey(entry.getKey())) {
				mMemoryMapping.put(entry.getKey(), entry.getValue());
			}
		}

		for (final Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {
			mIteratedMemory.put(entry.getKey(), null);
		}
	}

	/**
	 * update the iterated memory by using the symbolic memories of the backbones.
	 */
	public void updateMemory() {

		for (final Entry<IProgramVar, Term> entry : mIteratedMemory.entrySet()) {

			final Term symbol = mMemoryMapping.get(entry.getKey());

			Term update = symbol;

			caseType currentType = caseType.NOT_CHANGED;
			caseType prevCase = caseType.NOT_CHANGED;

			/**
			 * refine the iterated memory using the symbolic memories of each backbone.
			 */
			for (final Backbone backbone : mLoop.getBackbones()) {

				/**
				 * A new value can only be computed, iff the cases do not change.
				 */
				if (!currentType.equals(prevCase) && !prevCase.equals(caseType.NOT_CHANGED)) {
					update = null;
					mLogger.debug("None of the cases applicable " + entry.getKey() + " value = unknown");
					break;
				}

				final Term memory = backbone.getSymbolicMemory().getValue(entry.getKey());
				final TransFormula backboneTf = backbone.getFormula();

				/**
				 * Variable not changed in backbone
				 */
				if (memory == null || memory.equals(symbol) || memory instanceof TermVariable) {
					continue;
				}

				/**
				 * in each backbone the variable is either not changed or set to an expression
				 */
				if (memory instanceof ConstantTerm || !backboneTf.getAssignedVars().contains(entry.getKey())) {

					update = memory;
					prevCase = currentType;
					currentType = caseType.CONSTANT_ASSIGNMENT;

					mOverapprox = true;

					mLogger.debug("Assignment");
					continue;
				}

				/**
				 * If the variable is changed from its symbol by adding a constant for each backbone.
				 */

				if ("+".equals(((ApplicationTerm) memory).getFunction().getName())) {

					mLogger.debug("Addition");

					update = mScript.getScript().term("+", update, mScript.getScript().term("*",
							((ApplicationTerm) memory).getParameters()[1], backbone.getPathCounter()));

					prevCase = currentType;
					currentType = caseType.ADDITION;

				}

				/**
				 * If the variable is changed from its symbol by subtracting a constant for each backbone.
				 */
				if ("-".equals(((ApplicationTerm) memory).getFunction().getName())) {

					mLogger.debug("Subtraction");

					update = mScript.getScript().term("-", update, mScript.getScript().term("*",
							((ApplicationTerm) memory).getParameters()[1], backbone.getPathCounter()));

					prevCase = currentType;
					currentType = caseType.SUBTRACTION;

				}

				/**
				 * If the variable is multiplicated by a non constant term mark variable as unknown.
				 */
				if ("*".equals(((ApplicationTerm) memory).getFunction().getName())) {

					mIllegal.add(entry.getKey());

					mLogger.debug("Multiplication");
					update = mScript.getScript().term("*", update, mScript.getScript().term("*",
							((ApplicationTerm) memory).getParameters()[0], backbone.getPathCounter()));

					prevCase = currentType;
					currentType = caseType.MULTIPLICATION;

				}

				/**
				 * If the variable is assigned a constant assignment that contains a pathcounter.
				 */
				if (!Arrays.asList(((ApplicationTerm) memory).getParameters()).contains(symbol) && Arrays
						.asList(((ApplicationTerm) memory).getParameters()).contains(backbone.getPathCounter())) {

					mLogger.debug("Constant assignment");

					final Map<Term, Term> mapping = new HashMap<>();

					final Term newMapping = mScript.getScript().term("-", backbone.getPathCounter(),
							Rational.ONE.toTerm(SmtSortUtils.getIntSort(mScript)));
					mapping.put(backbone.getPathCounter(), newMapping);

					final Substitution sub = new Substitution(mScript, mapping);
					update = sub.transform(memory);
				}
			}
			mIteratedMemory.replace(entry.getKey(), update);
		}
		/**
		 * remove unknown variables.
		 */
		for (final IProgramVar var : mIllegal) {
			mOverapprox = true;
			mIteratedMemory.remove(var);
			mMemoryMapping.remove(var);
		}
	}

	/**
	 * Compute the abstract condition using the {@link IteratedSymbolicMemory} via the technique described in the paper.
	 */
	public void updateCondition() {

		/**
		 * going over all backbones to refine the accelerated loop summary.
		 */
		for (final Backbone backbone : mLoop.getBackbones()) {
			final List<TermVariable> freeVars = new ArrayList<>();
			final List<Term> terms = new ArrayList<>();

			/**
			 * entry condition of the backbone
			 */
			Term condition = mLoop.updateVars(backbone.getCondition().getFormula(), backbone.getCondition().getInVars(),
					backbone.getCondition().getOutVars());

			for (final TermVariable var : condition.getFreeVars()) {
				if (mPathCounters.contains(var)) {
					freeVars.add(var);
				}
			}

			// DD: Looks fishy ...
			if (condition instanceof QuantifiedFormula) {
				condition = ((QuantifiedFormula) condition).getSubformula();
			}

			final Map<Term, Term> mapping = new HashMap<>();

			final ApplicationTerm appTerm = (ApplicationTerm) condition;

			/**
			 * replace subterms from backbone condition with accelerated variables of the iterated memory.
			 */
			for (final Term term : appTerm.getParameters()) {
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

			/**
			 * following the technique in the paper we construct step by step an accelerated backbone condition.
			 */
			final Term t1 = mScript.getScript().term("<", mNewPathCounters.get(backbone.getPathCounter()),
					backbone.getPathCounter());
			final Term t2 = mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)),
					mNewPathCounters.get(backbone.getPathCounter()));

			Term tFirstPart = mScript.getScript().term("and", t1, t2);

			for (final TermVariable var : tempPathCounters) {
				terms.add(mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)),
						mNewPathCounters.get(var), var));
			}

			for (final TermVariable var : freeVars) {
				terms.add(mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)), var));
			}

			terms.add(newCondition);

			Term tBackPart = SmtUtils.and(mScript.getScript(), terms);
			terms.clear();

			if (!freeVars.isEmpty()) {
				tBackPart = mScript.getScript().quantifier(QuantifiedFormula.EXISTS,
						freeVars.toArray(new TermVariable[freeVars.size()]), tBackPart);
			}

			terms.add(tBackPart);
			tBackPart = SmtUtils.and(mScript.getScript(), terms);
			terms.clear();

			if (!tempNewPathCounters.isEmpty()) {
				tBackPart = mScript.getScript().quantifier(QuantifiedFormula.EXISTS,
						tempNewPathCounters.toArray(new TermVariable[tempNewPathCounters.size()]), tBackPart);
			}

			terms.add(tBackPart);
			tBackPart = SmtUtils.and(mScript.getScript(), terms);
			tFirstPart = Util.implies(mScript.getScript(), tFirstPart, tBackPart);

			final TermVariable[] vars = { mNewPathCounters.get(backbone.getPathCounter()) };

			/**
			 * necessary condition is the finished accelerated summary of the backbone.
			 */
			final Term necessaryCondition = mScript.getScript().quantifier(QuantifiedFormula.FORALL, vars, tFirstPart);

			mTerms.add(PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript, necessaryCondition,
					SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION));
		}

		final TransFormulaBuilder tfb = new TransFormulaBuilder(mInVars, mOutVars, true, null, true, null, false);
		final List<Term> terms = new ArrayList<>();

		for (final Entry<IProgramVar, TermVariable> outvar : mOutVars.entrySet()) {
			if (!checkIfVarContained(outvar.getValue(), mAbstractPathCondition)
					&& mIteratedMemory.containsKey(outvar.getKey())) {
				terms.add(mScript.getScript().term("=", outvar.getValue(), mIteratedMemory.get(outvar.getKey())));
			}
		}
		for (final TermVariable pathCounter : mPathCounters) {
			terms.add(mScript.getScript().term("<=", Rational.ZERO.toTerm(SmtSortUtils.getIntSort(mScript)),
					pathCounter));
		}

		mAbstractPathCondition = SmtUtils.or(mScript.getScript(), mTerms.toArray(new Term[mTerms.size()]));

		terms.add(mAbstractPathCondition);
		mAbstractPathCondition = SmtUtils.and(mScript.getScript(), terms.toArray(new Term[terms.size()]));
		tfb.setFormula(mAbstractPathCondition);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);

		tfb.addAuxVarsButRenameToFreshCopies(mNewPathCounters.keySet(), mScript);
		final Set<TermVariable> values = new HashSet<>(mLoop.getVars());

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
		final Term condition = backbone.getFormula().getFormula();
		final Map<Term, Term> subMapping = termUnravel(condition);
		final Substitution sub = new Substitution(mScript, subMapping);
		return sub.transform(condition);
	}

	/**
	 * Check if a given variable is contained in a given term.
	 *
	 * @param tv
	 * @param term
	 * @return
	 */
	private static boolean checkIfVarContained(final TermVariable tv, final Term term) {

		Term t = term;

		if (t instanceof TermVariable) {
			return t.equals(tv);
		}

		if (t instanceof ConstantTerm) {
			return false;
		}

		if (t instanceof QuantifiedFormula) {
			t = ((QuantifiedFormula) t).getSubformula();
		}

		final Deque<Term> stack = new ArrayDeque<>();
		stack.addAll(Arrays.asList(((ApplicationTerm) t).getParameters()));

		while (!stack.isEmpty()) {
			Term subTerm = stack.pop();
			if (subTerm instanceof ConstantTerm || subTerm instanceof TermVariable) {
				continue;
			}

			if (subTerm instanceof QuantifiedFormula) {
				subTerm = ((QuantifiedFormula) subTerm).getSubformula();
			}
			if (Arrays.asList(((ApplicationTerm) subTerm).getParameters()).contains(tv)
					&& "=".equals(((ApplicationTerm) subTerm).getFunction().getName())) {
				return true;
			}
			stack.addAll(Arrays.asList(((ApplicationTerm) subTerm).getParameters()));
		}
		return false;
	}

	/**
	 * Unravel a given term, which means substituting subterms with terms from the iterated memory
	 *
	 * @param term
	 * @return a substitution mapping
	 */
	private Map<Term, Term> termUnravel(final Term term) {
		final Map<Term, Term> result = new HashMap<>();
		if (term instanceof QuantifiedFormula || term instanceof ConstantTerm) {
			return result;
		}

		if (term instanceof TermVariable) {
			final TermVariable tv = (TermVariable) term;
			for (final Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {
				if (tv.equals(entry.getValue()) && !(mIteratedMemory.get(entry.getKey()) instanceof ConstantTerm)) {
					result.put(term, mIteratedMemory.get(entry.getKey()));
					break;
				}
			}
			return result;
		}

		final Deque<Term> stack = new ArrayDeque<>();
		stack.add(term);

		while (!stack.isEmpty()) {
			Term subTerm = stack.pop();
			if (subTerm instanceof ConstantTerm || subTerm instanceof TermVariable) {
				continue;
			}

			if (subTerm instanceof QuantifiedFormula) {
				subTerm = ((QuantifiedFormula) subTerm).getSubformula();
			}

			for (final Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {
				if (Arrays.asList(((ApplicationTerm) subTerm).getParameters()).contains(entry.getValue())
						&& !(mIteratedMemory.get(entry.getKey()) instanceof ConstantTerm)) {

					final Sort sort = subTerm.getSort();
					if (sort.equals(mScript.getScript().sort(SmtSortUtils.INT_SORT))) {
						result.put(subTerm, mIteratedMemory.get(entry.getKey()));
					}
					if (sort.equals(mScript.getScript().sort(SmtSortUtils.BOOL_SORT))) {
						for (final Term t : ((ApplicationTerm) subTerm).getParameters()) {
							result.putAll(termUnravel(t));
						}
					}
					continue;
				}
			}
			stack.addAll(Arrays.asList(((ApplicationTerm) subTerm).getParameters()));
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
		final Term condition = tf.getFormula();
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

	public boolean isOverapprox() {
		return mOverapprox;
	}
}
