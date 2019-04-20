/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.MultiElementCounter;

/**
 * Wrapper for an {@link Script} with additional locking mechanism. Additionally this class provides a mechanism to
 * construct fresh variables.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ManagedScript {
	private static final String MANAGED_SCRIPT_LOCKED_BY = "ManagedScript locked by ";
	protected final IUltimateServiceProvider mServices;
	protected final Script mScript;
	protected final ILogger mLogger;
	protected final VariableManager mVariableManager;
	private final SkolemFunctionManager mSkolemFunctionManager;

	private Object mLockOwner;

	public ManagedScript(final IUltimateServiceProvider services, final Script script) {
		super();
		mServices = services;
		mScript = script;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mVariableManager = new VariableManager();
		mSkolemFunctionManager = new SkolemFunctionManager();
	}

	public void lock(final Object lockOwner) {
		if (lockOwner == null) {
			throw new IllegalArgumentException("cannot be locked by null");
		}
		if (mLockOwner == null) {
			mLockOwner = lockOwner;
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(MANAGED_SCRIPT_LOCKED_BY + lockOwner.toString());
			}
		} else {
			throw new IllegalStateException("ManagedScript already locked by " + mLockOwner.toString());
		}
	}

	public void unlock(final Object lockOwner) {
		if (mLockOwner == null) {
			throw new IllegalStateException("ManagedScript not locked");
		}
		if (mLockOwner == lockOwner) {
			mLockOwner = null;
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("ManagedScript unlocked by " + lockOwner.toString());
			}
		} else {
			throw new IllegalStateException(MANAGED_SCRIPT_LOCKED_BY + mLockOwner.toString());
		}
	}

	public boolean isLocked() {
		return mLockOwner != null;
	}

	public boolean requestLockRelease() {
		if (mLockOwner == null) {
			throw new IllegalStateException("ManagedScript not locked");
		}
		if (mLockOwner instanceof ILockHolderWithVoluntaryLockRelease) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Asking " + mLockOwner + " to release lock");
			}
			((ILockHolderWithVoluntaryLockRelease) mLockOwner).releaseLock();
			return true;
		}
		return false;
	}

	public boolean isLockOwner(final Object allegedLockOwner) {
		return allegedLockOwner == mLockOwner;
	}

	public void push(final Object lockOwner, final int levels) throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		mScript.push(levels);
	}

	public void pop(final Object lockOwner, final int levels) throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		mScript.pop(levels);
	}

	public LBool assertTerm(final Object lockOwner, final Term term) throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.assertTerm(term);
	}

	public LBool checkSat(final Object lockOwner) throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.checkSat();
	}

	public Term[] getUnsatCore(final Object lockOwner) throws SMTLIBException, UnsupportedOperationException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.getUnsatCore();
	}

	public Term annotate(final Object lockOwner, final Term t, final Annotation... annotations) throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.annotate(t, annotations);
	}

	public Term term(final Object lockOwner, final String funcname, final Term... params) throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.term(funcname, params);
	}

	public Term term(final Object lockOwner, final String funcname, final BigInteger[] indices, final Sort returnSort,
			final Term... params) throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.term(funcname, indices, returnSort, params);
	}

	public Term let(final Object lockOwner, final TermVariable[] vars, final Term[] values, final Term body)
			throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.let(vars, values, body);
	}

	public void declareFun(final Object lockOwner, final String fun, final Sort[] paramSorts, final Sort resultSort)
			throws SMTLIBException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		mScript.declareFun(fun, paramSorts, resultSort);
	}

	public QuotedObject echo(final Object lockOwner, final QuotedObject msg) {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.echo(msg);
	}

	public Map<Term, Term> getValue(final Object lockOwner, final Term[] terms) {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.getValue(terms);
	}

	public Script getScript() {
		return mScript;
	}

	public Term[] getInterpolants(final Object lockOwner, final Term[] partition)
			throws SMTLIBException, UnsupportedOperationException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.getInterpolants(partition);
	}

	public Term[] getInterpolants(final Object lockOwner, final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		assert lockOwner == mLockOwner : generateLockErrorMessage(lockOwner, mLockOwner);
		return mScript.getInterpolants(partition, startOfSubtree);
	}

	private static String generateLockErrorMessage(final Object expectedLockOwner, final Object actualLockOwner) {
		if (actualLockOwner == null) {
			return "A " + expectedLockOwner.getClass().getSimpleName()
					+ " wants to use this ManagedScript without locking";
		} else {
			return "A " + expectedLockOwner.getClass().getSimpleName()
					+ " wants to use this ManagedScript but it is locked by some "
					+ actualLockOwner.getClass().getSimpleName();
		}
	}

	/**
	 * @param name
	 * @param sort
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript.VariableManager#constructFreshTermVariable(java.lang.String,
	 *      de.uni_freiburg.informatik.ultimate.logic.Sort)
	 */
	public TermVariable constructFreshTermVariable(final String name, final Sort sort) {
		return mVariableManager.constructFreshTermVariable(name, sort);
	}

	/**
	 * @param tv
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript.VariableManager#constructFreshCopy(de.uni_freiburg.informatik.ultimate.logic.TermVariable)
	 */
	public TermVariable constructFreshCopy(final TermVariable tv) {
		return mVariableManager.constructFreshCopy(tv);
	}

	/**
	 * @param varname
	 * @param sort
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript.VariableManager#variable(java.lang.String,
	 *      de.uni_freiburg.informatik.ultimate.logic.Sort)
	 */
	public TermVariable variable(final String varname, final Sort sort) {
		return mVariableManager.variable(varname, sort);
	}

	/**
	 * Given a function signature, this gives a fresh (i.e., not yet used in the current scope) name for a skolem
	 * function.
	 *
	 * @param parameterSorts
	 * @param resultSort
	 * @return
	 */
	public String constructFreshSkolemFunctionName(final Sort[] parameterSorts, final Sort resultSort) {
		return mSkolemFunctionManager.constructFreshSkolemFunctionName(parameterSorts, resultSort);
	}

	@FunctionalInterface
	public interface ILockHolderWithVoluntaryLockRelease {
		void releaseLock();
	}

	/**
	 * Constructs fresh TermVariables (i.e., TermVariables that have not been used before). Each constructed
	 * TermVariable is named as follows. The name start with the prefix "v_". Next follows the "basename" which is a
	 * name given by the caller of the VariableManager. The name ends with the suffix "_n" where n is number that we use
	 * to ensure that each variable is unique.
	 *
	 * @author Matthias Heizmann
	 */
	private class VariableManager {

		/**
		 * Counter for the construction of fresh variables.
		 */
		private final MultiElementCounter<String> mTvForBasenameCounter = new MultiElementCounter<>();

		/**
		 * Whenever we construct a TermVariable we store its basename. This is the name for that the TermVariable was
		 * constructed. Whenever we have to construct a fresh copy of a TermVariable we use the basename of this
		 * TermVariable to obtain a unique but very similar name for the new copy.
		 */
		private final Map<TermVariable, String> mTv2Basename = new HashMap<>();

		private final Set<String> mVariableNames = new HashSet<>();

		/**
		 * Construct "fresh" TermVariables. In mathematical logics a variable is called "fresh" if the variable has not
		 * occurred in the same context. TermVariables constructed by objects that implement this interface are
		 * guaranteed to have a name which is different form all other TermVariables constructed by this object. There
		 * is no guarantee that a similar variable was not constructed with the same Script.
		 *
		 * @param name
		 *            String that will occur as substring of the resulting TermVariable.
		 * @param sort
		 *            Sort of the resulting TermVariable.
		 * @return TermVariable whose name is different from the names of all other TermVariable that have been
		 *         constructed by this object.
		 */
		public TermVariable constructFreshTermVariable(final String name, final Sort sort) {
			if (name.contains("|")) {
				throw new IllegalArgumentException("Name contains SMT quote characters " + name);
			}
			final Integer newIndex = mTvForBasenameCounter.increment(name);
			final TermVariable result = mScript.variable("v_" + name + "_" + newIndex, sort);
			mTv2Basename.put(result, name);
			return result;
		}

		/**
		 * Construct a copy of an existing {@link TermVariable} that is fresh but has a very similar name.
		 *
		 * @see mTv2Basename
		 */
		public TermVariable constructFreshCopy(final TermVariable tv) {
			String basename = mTv2Basename.get(tv);
			if (basename == null) {
				mLogger.warn("TermVariabe " + tv
						+ " not constructed by VariableManager. Cannot ensure absence of name clashes.");
				basename = SmtUtils.removeSmtQuoteCharacters(tv.getName());
			}
			final TermVariable result = constructFreshTermVariable(basename, tv.getSort());
			return result;
		}

		/**
		 * Construct variable but check if variable with this name was already constructed.
		 */
		public TermVariable variable(final String varname, final Sort sort) {
			if (mVariableNames.contains(varname)) {
				throw new IllegalArgumentException("A variable with that name was already constructed: " + varname);
			}
			final TermVariable result = mScript.variable(varname, sort);
			mTv2Basename.put(result, varname);
			return result;
		}
	}

	private class SkolemFunctionManager {

		private static final String SKOLEM_PREFIX = "skolem";

		private int counter;

		public String constructFreshSkolemFunctionName(final Sort[] parameterSorts, final Sort resultSort) {
			// TODO: give nicer name, perhaps using the signature
			return SKOLEM_PREFIX + counter++;
		}
	}
}
