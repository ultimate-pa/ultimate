package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
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

	private final Map<IProgramVar, Term> mMemoryMapping;
	private final ManagedScript mScript;
	private final ILogger mLogger;
	private final IIcfgSymbolTable mOldSymbolTable;

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
		mMemoryMapping = new HashMap<>();

		// set all variables to the InVars (symbols):
		for (Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			mMemoryMapping.put(entry.getKey(), entry.getValue());
		}
	}

	/**
	 * Update the memory with changed values.
	 * 
	 * @param value
	 *            A mapping of {@link IProgramVar} to their new changed value.
	 */
	public void updateVars(Map<IProgramVar, Term> value) {

		for (final Map.Entry<IProgramVar, Term> entry : value.entrySet()) {
			ApplicationTerm appTerm = (ApplicationTerm) entry.getValue();

			final Map<Term, Term> substitution = new HashMap<>();

			for (Term term : appTerm.getParameters()) {
				if (term instanceof TermVariable
						&& mMemoryMapping.containsKey(mOldSymbolTable.getProgramVar((TermVariable) term))) {
					substitution.put(term, mMemoryMapping.get(mOldSymbolTable.getProgramVar((TermVariable) term)));
				}
			}

			final Substitution sub = new Substitution(mScript, substitution);
			final Term t = sub.transform(appTerm);
			mMemoryMapping.replace(entry.getKey(), t);
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
	public Term getValue(TermVariable var) {
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
