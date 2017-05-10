package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.werner;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
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
			final IIcfgSymbolTable oldSymbolTable, Loop loop, List<TermVariable> pathCounters) {

		super(script, logger, tf, oldSymbolTable);
		mIteratedMemory = new HashMap<>();
		mPathCounters = pathCounters;

		for (Entry<IProgramVar, Term> entry : mMemoryMapping.entrySet()) {
			mIteratedMemory.put(entry.getKey(), null);
		}
		mLoop = loop;
		mLogger.debug("Iterated Memory: " + mIteratedMemory);

	}

	/**
	 * update the memories by using the symbolic memories of the backbones.
	 */
	public void updateMemory() {

		for (Entry<IProgramVar, Term> entry : mIteratedMemory.entrySet()) {

			final Term symbol = mMemoryMapping.get(entry.getKey());
			Term update = symbol;

			for (Backbone backbone : mLoop.getBackbones()) {

				final Term memory = backbone.getSymbolicMemory().getValue(entry.getKey());

				// @TODO: variable not changed in backbone
				if (memory == null) {
					continue;
				}

				mLogger.debug("Symbol: " + mMemoryMapping.get(entry.getKey()));
				mLogger.debug("BackMem: " + memory);

				if (memory instanceof TermVariable || memory instanceof ConstantTerm) {
					update = memory;
					continue;
				}

				// if the variable is changed from its symbol by adding a
				// constant for each backbone.
				if (!(memory instanceof TermVariable) && !memory.equals(symbol)
						&& "+".equals(((ApplicationTerm) memory).getFunction().getName())) {
					mLogger.debug("Not equal");

					update = mScript.getScript().term("+", update, mScript.getScript().term("*",
							((ApplicationTerm) memory).getParameters()[1], (Term) backbone.getPathCounter()));

					mLogger.debug("Update: " + update);
				}

				if (!(memory instanceof TermVariable) && !memory.equals(symbol)
						&& "=".equals(((ApplicationTerm) memory).getFunction().getName())) {
					update = mScript.getScript().term("+", update, mScript.getScript().term("*",
							((ApplicationTerm) memory).getParameters()[1], (Term) backbone.getPathCounter()));
					mLogger.debug("Zuweisung");
				}
			}
			mIteratedMemory.replace(entry.getKey(), update);
		}
		mLogger.debug("Iterated Memory: " + mIteratedMemory);
	}

	public Map<IProgramVar, Term> getIteratedMemory() {
		return mIteratedMemory;
	}
	
	public List<TermVariable> getPathCounters() {
		return mPathCounters;
	}
}
