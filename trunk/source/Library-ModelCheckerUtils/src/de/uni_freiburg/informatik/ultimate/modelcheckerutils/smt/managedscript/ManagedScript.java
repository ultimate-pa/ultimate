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

/**
 * Wrapper for an {@link Script} with additional locking mechanism.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ManagedScript {
	
	private final IUltimateServiceProvider mServices;
	private final Script mScript;
	private final ILogger mLogger;
	
	private Object mLockOwner = null;
	
	public ManagedScript(IUltimateServiceProvider services, Script script) {
		super();
		mServices = services;
		mScript = script;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
	}
	
	public void lock(Object lockOwner) {
		if (lockOwner == null) {
			throw new NullPointerException("cannot be locked by null");
		} else {
			if (mLockOwner == null) {
				mLockOwner = lockOwner;
				mLogger.debug("ManagedScript locked by " + lockOwner.toString());
			} else {
				throw new IllegalStateException("ManagedScript already locked by " + mLockOwner.toString());
			}
		}
	}
	
	public void unlock(Object lockOwner) {
		if (mLockOwner == null) {
			throw new IllegalStateException("ManagedScript not locked");
		} else {
			if (mLockOwner == lockOwner) {
				mLockOwner = null;
				mLogger.debug("ManagedScript unlocked by " + lockOwner.toString());
			} else {
				throw new IllegalStateException("ManagedScript locked by " + mLockOwner.toString());
			}
		}
	}
	
	public boolean isLocked() {
		return mLockOwner != null;
	}
	
	public boolean requestLockRelease() {
		if (mLockOwner == null) {
			throw new IllegalStateException("ManagedScript not locked");
		} else {
			if (mLockOwner instanceof ILockHolderWithVoluntaryLockRelease) {
				mLogger.debug("Asking " + mLockOwner + " to release lock");
				((ILockHolderWithVoluntaryLockRelease) mLockOwner).releaseLock();
				return true;
			} else {
				return false;
			}
		}
	}
	
	public boolean isLockOwner(Object allegedLockOwner) {
		return allegedLockOwner == mLockOwner;
	}
	
	public interface ILockHolderWithVoluntaryLockRelease {
		public void releaseLock();
	}
	
	public void push(Object lockOwner, int levels) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		mScript.push(levels);
	}
	public void pop(Object lockOwner, int levels) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		mScript.pop(levels);
	}
	public LBool assertTerm(Object lockOwner, Term term) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.assertTerm(term);
	}
	public LBool checkSat(Object lockOwner) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.checkSat();
	}
	public Term[] getUnsatCore(Object lockOwner) throws SMTLIBException, UnsupportedOperationException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.getUnsatCore();
	}
	public Term annotate(Object lockOwner, Term t, Annotation... annotations) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.annotate(t, annotations);
	}

	public Term term(Object lockOwner, String funcname, Term... params) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.term(funcname, params);
	}

	public Term term(Object lockOwner, String funcname, BigInteger[] indices, Sort returnSort, Term... params) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.term(funcname, indices, returnSort, params);
	}

	public Term let(Object lockOwner, TermVariable[] vars, Term[] values, Term body) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.let(vars, values, body);
	}

	public void declareFun(Object lockOwner, String fun, Sort[] paramSorts, Sort resultSort) throws SMTLIBException {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		mScript.declareFun(fun, paramSorts, resultSort);
	}

	public QuotedObject echo(Object lockOwner, QuotedObject msg) {
		assert lockOwner == mLockOwner : "ManagedScript locked by " + mLockOwner;
		return mScript.echo(msg);
	}

	public Script getScript() {
		return mScript;
	}
	
}
