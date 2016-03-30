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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
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
	
	private final IUltimateServiceProvider m_Services;
	private final Script m_Script;
	private final Logger m_Logger;
	
	private Object m_LockOwner = null;
	
	public ManagedScript(IUltimateServiceProvider services, Script script) {
		super();
		m_Services = services;
		m_Script = script;
		m_Logger = m_Services.getLoggingService().getLogger(ModelCheckerUtils.sPluginID);
	}
	
	public void lock(Object lockOwner) {
		if (lockOwner == null) {
			throw new NullPointerException("cannot be locked by null");
		} else {
			if (m_LockOwner == null) {
				m_LockOwner = lockOwner;
				m_Logger.debug("ManagedScript locked by " + lockOwner.toString());
			} else {
				throw new IllegalStateException("ManagedScript already locked by " + m_LockOwner.toString());
			}
		}
	}
	
	public void unlock(Object lockOwner) {
		if (m_LockOwner == null) {
			throw new IllegalStateException("ManagedScript not locked");
		} else {
			if (m_LockOwner == lockOwner) {
				m_LockOwner = null;
				m_Logger.debug("ManagedScript unlocked by " + lockOwner.toString());
			} else {
				throw new IllegalStateException("ManagedScript locked by " + m_LockOwner.toString());
			}
		}
	}
	
	public boolean isLocked() {
		return m_LockOwner != null;
	}
	
	public boolean requestLockRelease() {
		if (m_LockOwner == null) {
			throw new IllegalStateException("ManagedScript not locked");
		} else {
			if (m_LockOwner instanceof ILockHolderWithVoluntaryLockRelease) {
				m_Logger.debug("Asking " + m_LockOwner + " to release lock");
				((ILockHolderWithVoluntaryLockRelease) m_LockOwner).releaseLock();
				return true;
			} else {
				return false;
			}
		}
	}
	
	public boolean isLockOwner(Object allegedLockOwner) {
		return allegedLockOwner == m_LockOwner;
	}
	
	public interface ILockHolderWithVoluntaryLockRelease {
		public void releaseLock();
	}
	
	public void push(Object lockOwner, int levels) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		m_Script.push(levels);
	}
	public void pop(Object lockOwner, int levels) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		m_Script.pop(levels);
	}
	public LBool assertTerm(Object lockOwner, Term term) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.assertTerm(term);
	}
	public LBool checkSat(Object lockOwner) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.checkSat();
	}
	public Term[] getUnsatCore(Object lockOwner) throws SMTLIBException, UnsupportedOperationException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.getUnsatCore();
	}
	public Term annotate(Object lockOwner, Term t, Annotation... annotations) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.annotate(t, annotations);
	}

	public Term term(Object lockOwner, String funcname, Term... params) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.term(funcname, params);
	}

	public Term term(Object lockOwner, String funcname, BigInteger[] indices, Sort returnSort, Term... params) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.term(funcname, indices, returnSort, params);
	}

	public Term let(Object lockOwner, TermVariable[] vars, Term[] values, Term body) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.let(vars, values, body);
	}

	public void declareFun(Object lockOwner, String fun, Sort[] paramSorts, Sort resultSort) throws SMTLIBException {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		m_Script.declareFun(fun, paramSorts, resultSort);
	}

	public QuotedObject echo(Object lockOwner, QuotedObject msg) {
		assert lockOwner == m_LockOwner : "ManagedScript locked by " + m_LockOwner;
		return m_Script.echo(msg);
	}
}
