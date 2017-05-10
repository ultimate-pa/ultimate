package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.HashMap;
import java.util.Map;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
	protected final IIcfgSymbolTable mOldSymbolTable;

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
	public SymbolicMemory(final ManagedScript script, final ILogger logger, final TransFormula tf,
			final IIcfgSymbolTable oldSymbolTable) {

		mScript = script;
		mLogger = logger;
		mOldSymbolTable = oldSymbolTable;

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
					&& mMemoryMapping.containsKey(mOldSymbolTable.getProgramVar((TermVariable) t))) {
				substitution.put(t, mMemoryMapping.get(mOldSymbolTable.getProgramVar((TermVariable) t)));

			} else {
				final ApplicationTerm appTerm = (ApplicationTerm) t;
				for (Term term : appTerm.getParameters()) {
					if (term instanceof TermVariable
							&& mMemoryMapping.containsKey(mOldSymbolTable.getProgramVar((TermVariable) term))) {
						substitution.put(term, mMemoryMapping.get(mOldSymbolTable.getProgramVar((TermVariable) term)));
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
