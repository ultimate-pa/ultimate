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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * A symbolic memory
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 */

public class SymbolicMemory {

	protected final Map<IProgramVar, Term> mMemoryMapping;
	protected final ManagedScript mScript;
	protected final ILogger mLogger;

	/**
	 * Construct a new Symbolic Memory.
	 * 
	 * @param script
	 *            A {@link ManagedScript} instance that can be used to perform
	 *            SMT operations.
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
	public SymbolicMemory(final ManagedScript script, final ILogger logger, final TransFormula tf) {

		mScript = script;
		mLogger = logger;

		// set all variables to the InVars (symbols):
		mMemoryMapping = LoopDetector.calculateSymbolTable(tf);
	}

	/**
	 * Update the memory with changed values.
	 * 
	 * @param value
	 *            A mapping of {@link IProgramVar} to their new changed value.
	 */
	public void updateVars(Map<IProgramVar, Term> value) {
		
		for (final Map.Entry<IProgramVar, Term> entry : value.entrySet()) {

			final Term t = entry.getValue();
			final Map<Term, Term> substitution = new HashMap<>();

			if (t instanceof TermVariable
					&& mMemoryMapping.containsKey(entry.getKey())) {
				substitution.put(t, mMemoryMapping.get(entry.getKey()));

			}
			
			if (t instanceof ConstantTerm) {
				mLogger.debug(t + " " + entry.getKey().getTermVariable().toString() + " " + mMemoryMapping.get(entry.getKey()));
				substitution.put(mMemoryMapping.get(entry.getKey()), t);
			} else {
				final ApplicationTerm appTerm = (ApplicationTerm) t;
				for (Term term : appTerm.getParameters()) {
					if (term instanceof TermVariable
							&& mMemoryMapping.containsKey(entry.getKey())) {
						substitution.put(term, mMemoryMapping.get(entry.getKey()));
					}
				}
			}

			final Substitution sub = new Substitution(mScript, substitution);
			final Term t2 = sub.transform(t);
			mMemoryMapping.replace(entry.getKey(), t2);
		}
		mLogger.debug("the Memory: " + mMemoryMapping.toString());
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

}
