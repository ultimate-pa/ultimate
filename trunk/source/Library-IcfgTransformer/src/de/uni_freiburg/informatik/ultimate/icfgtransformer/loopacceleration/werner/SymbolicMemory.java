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

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * A symbolic memory
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class SymbolicMemory {

	private final IUltimateServiceProvider mServices;
	private final Map<IProgramVar, Term> mMemoryMapping;
	private final ManagedScript mScript;
	private final IIcfgSymbolTable mOldSymbolTable;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;

	/**
	 * Construct a new Symbolic Memory.
	 * 
	 * @param script
	 *            A {@link ManagedScript} instance that can be used to perform
	 *            SMT operations.
	 * 
	 * @param services
	 *            an {@link IUltimateServiceProvider}
	 * 
	 * @param logger
	 *            A {@link ILogger} instance that is used for debug logging.
	 * 
	 * @param tf
	 *            A {@link TransFormula} for which the memory is built.
	 * @param oldSymbolTable
	 *            A {@link IIcfgSymbolTable} for translating
	 *            {@link TermVariable} to an {@link IProgramVar} for changing in
	 *            the memory.
	 */
	public SymbolicMemory(final ManagedScript script, final IUltimateServiceProvider services, final TransFormula tf,
			final IIcfgSymbolTable oldSymbolTable) {

		mScript = script;
		mServices = services;
		mOldSymbolTable = oldSymbolTable;
		mInVars = tf.getInVars();
		mOutVars = tf.getOutVars();
		mMemoryMapping = new HashMap<>();

		/**
		 * initialize the symbolic memory.
		 */
		for (final Entry<IProgramVar, TermVariable> entry : mInVars.entrySet()) {
			mMemoryMapping.put(entry.getKey(), (TermVariable) entry.getValue());
		}

		for (final Entry<IProgramVar, TermVariable> entry : mOutVars.entrySet()) {
			if (!mMemoryMapping.containsKey(entry.getKey())) {
				mMemoryMapping.put(entry.getKey(), (TermVariable) entry.getValue());
			}
		}
	}

	/**
	 * Update the memory with changed values.
	 * 
	 * @param value
	 *            A mapping of {@link IProgramVar} to their new changed value.
	 */
	public void updateVars(final Map<IProgramVar, Term> value) {

		for (final Map.Entry<IProgramVar, Term> entry : value.entrySet()) {

			final Term t = entry.getValue();
			final Map<Term, Term> substitution = new HashMap<>();

			if (t instanceof TermVariable && mMemoryMapping.containsKey(entry.getKey())) {
				substitution.put(t, mMemoryMapping.get(entry.getKey()));
			}

			if (t instanceof TermVariable && !mMemoryMapping.containsKey(entry.getKey())) {
				mMemoryMapping.put(entry.getKey(), entry.getValue());
				continue;
			}

			if (t instanceof ConstantTerm) {
				substitution.put(mMemoryMapping.get(entry.getKey()), t);
			} else if (substitution.isEmpty()) {
				final ApplicationTerm appTerm = (ApplicationTerm) t;
				substitution.putAll(termUnravel(appTerm));
			}

			final Substitution sub = new Substitution(mScript, substitution);
			final Term t2 = sub.transform(t);
			mMemoryMapping.replace(entry.getKey(), t2);
		}
	}

	/**
	 * Update the given transformula with entries of the symbolic memory.
	 * 
	 * @param tf
	 *            {@link TransFormula}
	 * @return a symbolic memory compatible {@link TransFormula}
	 */
	public UnmodifiableTransFormula updateCondition(final UnmodifiableTransFormula tf) {

		final Term t = tf.getFormula();

		if (t instanceof QuantifiedFormula) {
			return null;
		}

		final ApplicationTerm appTerm = (ApplicationTerm) tf.getFormula();
		final Map<Term, Term> substitution = new HashMap<>();

		substitution.putAll(termUnravel(appTerm, tf.getInVars()));

		final Substitution sub = new Substitution(mScript, substitution);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(mInVars, mOutVars, true, null, true, null, true);
		final Term term = sub.transform(tf.getFormula());

		tfb.setFormula(SmtUtils.simplify(mScript, term, mServices, SimplificationTechnique.SIMPLIFY_DDA));
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);

		return tfb.finishConstruction(mScript);

	}

	/**
	 * Unravel a given term and substitute subterms with values from the
	 * symbolic memory.
	 * 
	 * @param appTerm
	 * @return
	 */
	private Map<Term, Term> termUnravel(final Term term) {

		final Map<Term, Term> result = new HashMap<>();

		if (term instanceof TermVariable) {

			if (mMemoryMapping.containsKey(mOldSymbolTable.getProgramVar((TermVariable) term))) {
				result.put(term, mMemoryMapping.get(mOldSymbolTable.getProgramVar((TermVariable) term)));
			}
			return result;
		}

		if (term instanceof ConstantTerm) {
			return result;
		}

		final ApplicationTerm appTerm = (ApplicationTerm) term;
		for (final Term subTerm : appTerm.getParameters()) {
			result.putAll(termUnravel(subTerm));
		}
		return result;
	}

	/**
	 * Unravel a given term and substitute subterms with values from the
	 * symbolic memory.
	 * 
	 * @param appTerm
	 * @param progVars
	 * @return
	 */
	private Map<Term, Term> termUnravel(final Term term, final Map<IProgramVar, TermVariable> progVars) {

		final Map<Term, Term> result = new HashMap<>();

		if (term instanceof TermVariable) {

			for (final Entry<IProgramVar, TermVariable> entry : progVars.entrySet()) {
				if (entry.getValue().equals(term) && (mMemoryMapping.containsKey(entry.getKey()))
						&& !(mMemoryMapping.get(entry.getKey()) instanceof ConstantTerm)) {
					result.put(term, mMemoryMapping.get(entry.getKey()));
				}
			}
			return result;
		}

		if (term instanceof ConstantTerm) {
			return result;
		}

		final ApplicationTerm appTerm = (ApplicationTerm) term;
		for (final Term subTerm : appTerm.getParameters()) {
			result.putAll(termUnravel(subTerm, progVars));
		}
		return result;
	}

	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}

	/**
	 * get the value of a specific variable in the memory.
	 * 
	 * @param var
	 *            A {@link TermVariable} for which the memory value is wanted.
	 * 
	 * @return The memory value of the {@link TermVariable}.
	 */
	public Term getValue(final IProgramVar var) {
		return mMemoryMapping.get(var);
	}

	/**
	 * Get the whole symbolic memory.
	 * 
	 * @return The whole symbolic memory
	 */
	public Map<IProgramVar, Term> getMemory() {
		return mMemoryMapping;
	}

	public Map<IProgramVar, TermVariable> getVars() {
		final Map<IProgramVar, TermVariable> result = new HashMap<>();
		for (final Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {
			result.put(entry.getKey(), (TermVariable) entry.getValue());
		}
		return result;
	}

}
