/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE KInduction Library.
 *
 * The ULTIMATE KInduction Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE KInduction Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE KInduction Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE KInduction Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE KInduction Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.kinduction.encoding;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * The activation records of the recursive procedures, as ordinary program variables.
 * <p>
 * {@link ProcedureSummaries} resolves a call either into a summary - which needs the callee's summary to exist
 * already - or by unfolding a copy of the callee's states per call site. A call cycle defeats both: there is no order
 * in which the summaries exist, and the unfolding does not terminate. Both are really the same missing thing. The
 * unfolding distinguishes two activations of a procedure <em>in the graph</em>, so the graph has to be as big as the
 * call tree; a cycle makes that tree infinite. Distinguishing them <em>in the state</em> instead costs a fixed number
 * of variables, whatever the depth:
 * <ul>
 * <li>{@code ki_sp}, the stack pointer,
 * <li>{@code ki_ret}, an array mapping a stack index to the call site the activation at that index must return to,
 * <li>one array {@code ki_stack_l} per local variable {@code l} of a recursive procedure, mapping a stack index to
 * the value {@code l} had in the activation at that index.
 * </ul>
 * A call pushes (the caller's locals, the return site, {@code sp+1}), a return pops. The procedure's states then
 * occur exactly once in the graph, and its recursive call is an ordinary loop of it.
 * <p>
 * Nothing else in the encoding has to know: {@link PcTransitionSystem} takes its state vector from the in- and
 * outvars of the edge formulas it is given ({@code collectVars}) and frames whatever an edge does not assign, so
 * these variables behave like any other program variable of the analysed program.
 * <p>
 * The arrays are indexed by {@code Int} and are never constrained to be empty or non-negative at the start. They do
 * not have to be: a path can only reach a callee's exit node by going through the call edge that pushed, so every
 * {@code select} on a path is preceded by the matching {@code store}, and only the difference of the indices
 * matters, not where they start.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class CallStack {

	private static final String SP = "ki_sp";
	private static final String RET = "ki_ret";
	private static final String SLOT_PREFIX = "ki_stack_";

	private final ManagedScript mMgdScript;
	private final Script mScript;
	private final Sort mIndexSort;
	private final IProgramNonOldVar mStackPointer;
	private final IProgramNonOldVar mReturnSites;
	/** One array variable per local that an activation has to keep its own copy of. */
	private final Map<IProgramVar, IProgramNonOldVar> mSlots = new LinkedHashMap<>();

	/**
	 * @param locals
	 *            every local variable of every stack-encoded procedure. Minting the variables takes the script's
	 *            lock, so this has to happen while the loop tree is being built - before {@code KInduction.run} takes
	 *            it for the solver queries.
	 */
	public CallStack(final ManagedScript mgdScript, final Collection<? extends IProgramVar> locals) {
		mMgdScript = mgdScript;
		mScript = mgdScript.getScript();
		mIndexSort = SmtSortUtils.getIntSort(mScript);
		// Minting a program variable declares its default and primed constant, which the ManagedScript only lets
		// its lock owner do. Unlike ProgramVarUtils#constructConstantForAuxVar, constructGlobalProgramVarPair does
		// not take the lock itself.
		mMgdScript.lock(this);
		try {
			mStackPointer = ProgramVarUtils.constructGlobalProgramVarPair(SP, mIndexSort, mMgdScript, this);
			mReturnSites = ProgramVarUtils.constructGlobalProgramVarPair(RET,
					SmtSortUtils.getArraySort(mScript, mIndexSort, mIndexSort), mMgdScript, this);
			for (final IProgramVar local : locals) {
				final Sort slotSort =
						SmtSortUtils.getArraySort(mScript, mIndexSort, local.getTermVariable().getSort());
				mSlots.put(local, ProgramVarUtils.constructGlobalProgramVarPair(
						SLOT_PREFIX + local.getGloballyUniqueId(), slotSort, mMgdScript, this));
			}
		} finally {
			mMgdScript.unlock(this);
		}
	}

	/** The variables this encoding adds to the program, for logging and for the counterexample builder. */
	public Set<IProgramVar> getVariables() {
		final Set<IProgramVar> result = new LinkedHashSet<>();
		result.add(mStackPointer);
		result.add(mReturnSites);
		result.addAll(mSlots.values());
		return result;
	}

	public IProgramVar getStackPointer() {
		return mStackPointer;
	}

	/**
	 * Entering an activation: remember where it has to return to, remember the values {@code toSave} has in the
	 * caller, and move the stack pointer up.
	 * <p>
	 * {@code toSave} is empty unless the caller can be re-entered while the callee is running, i.e. unless caller and
	 * callee lie on a common call cycle - the locals of a caller that cannot be re-entered are never overwritten and
	 * need no copy.
	 */
	public UnmodifiableTransFormula push(final int returnSiteId, final Collection<IProgramVar> toSave) {
		final Map<IProgramVar, TermVariable> inVars = new LinkedHashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new LinkedHashMap<>();
		final List<Term> conjuncts = new ArrayList<>();

		final TermVariable sp = in(inVars, outVars, mStackPointer, false);
		final TermVariable spOut = out(outVars, mStackPointer);
		conjuncts.add(SmtUtils.binaryEquality(mScript, spOut,
				SmtUtils.sum(mScript, mIndexSort, sp, index(1))));

		final TermVariable ret = in(inVars, outVars, mReturnSites, false);
		conjuncts.add(SmtUtils.binaryEquality(mScript, out(outVars, mReturnSites),
				SmtUtils.store(mScript, ret, sp, index(returnSiteId))));

		for (final IProgramVar local : toSave) {
			final IProgramNonOldVar slot = slotOf(local);
			// The local itself is only read, so its invar is its outvar and the frame keeps it unchanged.
			final TermVariable value = in(inVars, outVars, local, true);
			final TermVariable slotIn = in(inVars, outVars, slot, false);
			conjuncts.add(SmtUtils.binaryEquality(mScript, out(outVars, slot),
					SmtUtils.store(mScript, slotIn, sp, value)));
		}
		return build(inVars, outVars, SmtUtils.and(mScript, conjuncts));
	}

	/**
	 * Leaving an activation: check that it is the one that was entered from {@code returnSiteId}, move the stack
	 * pointer down and give {@code toRestore} back the values the caller left them with.
	 * <p>
	 * {@code toRestore} must not contain a variable the return statement itself assigns - that one carries the
	 * result out of the activation being left, and the composition puts the return assignment before this formula
	 * for exactly that reason.
	 */
	public UnmodifiableTransFormula pop(final int returnSiteId, final Collection<IProgramVar> toRestore) {
		final Map<IProgramVar, TermVariable> inVars = new LinkedHashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new LinkedHashMap<>();
		final List<Term> conjuncts = new ArrayList<>();

		final TermVariable sp = in(inVars, outVars, mStackPointer, false);
		final TermVariable spOut = out(outVars, mStackPointer);
		conjuncts.add(SmtUtils.binaryEquality(mScript, spOut,
				SmtUtils.minus(mScript, sp, index(1))));

		final TermVariable ret = in(inVars, outVars, mReturnSites, true);
		conjuncts.add(SmtUtils.binaryEquality(mScript, SmtUtils.select(mScript, ret, spOut),
				index(returnSiteId)));

		for (final IProgramVar local : toRestore) {
			final IProgramNonOldVar slot = slotOf(local);
			final TermVariable slotIn = in(inVars, outVars, slot, true);
			conjuncts.add(SmtUtils.binaryEquality(mScript, out(outVars, local),
					SmtUtils.select(mScript, slotIn, spOut)));
		}
		return build(inVars, outVars, SmtUtils.and(mScript, conjuncts));
	}

	private IProgramNonOldVar slotOf(final IProgramVar local) {
		final IProgramNonOldVar slot = mSlots.get(local);
		if (slot == null) {
			throw new AssertionError("no stack slot for " + local + "; the variable of a stack-encoded procedure "
					+ "must be declared when the CallStack is constructed");
		}
		return slot;
	}

	/**
	 * An invar for {@code pv}. With {@code unchanged}, the same {@link TermVariable} also becomes its outvar, which
	 * is how a {@link UnmodifiableTransFormula} says "read but not written".
	 */
	private TermVariable in(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final IProgramVar pv, final boolean unchanged) {
		final TermVariable tv = mMgdScript.constructFreshCopy(pv.getTermVariable());
		inVars.put(pv, tv);
		if (unchanged) {
			outVars.put(pv, tv);
		}
		return tv;
	}

	private TermVariable out(final Map<IProgramVar, TermVariable> outVars, final IProgramVar pv) {
		final TermVariable tv = mMgdScript.constructFreshCopy(pv.getTermVariable());
		outVars.put(pv, tv);
		return tv;
	}

	private UnmodifiableTransFormula build(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Term formula) {
		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(inVars, outVars, true, null, true, null, true);
		tfb.setFormula(formula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mMgdScript);
	}

	private Term index(final int value) {
		return SmtUtils.constructIntValue(mScript, BigInteger.valueOf(value));
	}
}
