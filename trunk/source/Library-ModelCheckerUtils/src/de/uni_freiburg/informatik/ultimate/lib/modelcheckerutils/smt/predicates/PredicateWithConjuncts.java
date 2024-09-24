/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

/**
 * A predicate with a list of conjuncts. The conjunction formula is not computed eagerly.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class PredicateWithConjuncts implements IPredicate {
	protected final int mSerial;
	protected final ImmutableList<IPredicate> mConjuncts;
	protected final Script mScript;
	private Term mFormula;
	private Term mClosedFormula;
	private final String[] mProcedures;
	private final Set<IProgramVar> mVars;
	private final Set<IProgramFunction> mFuns;
	private IPredicate mOld;
	private IPredicate mNew;

	/**
	 * Create a new instance from scratch.
	 *
	 * @param serialNumber
	 *            The predicate's serial number
	 * @param conjuncts
	 *            The list of conjuncts
	 * @param script
	 *            A script to handle conjunction of terms.
	 */
	public PredicateWithConjuncts(final int serialNumber, final ImmutableList<IPredicate> conjuncts,
			final Script script) {
		mSerial = serialNumber;
		mConjuncts = conjuncts;
		mScript = script;
		mProcedures = new String[0];
		mVars = new HashSet<>();
		mFuns = new HashSet<>();

	}

	/**
	 * Creates a new instance as conjunction of two given predicates.
	 *
	 * @param serialNumber
	 *            The predicate's serial number
	 * @param old
	 *            The first conjunct, which also contains the predicate's locations. May itself be another instance of
	 *            this class.
	 * @param newConjunct
	 *            A new conjunct to be added. Should not be an instance of this class (otherwise, nesting occurs).
	 * @param script
	 *            A script to handle conjunction of terms.
	 */
	public PredicateWithConjuncts(final int serialNumber, final IPredicate old, final IPredicate newConjunct,
			final Script script) {
		mSerial = serialNumber;
		mScript = script;
		mProcedures = new String[0];
		mVars = new HashSet<>();
		mFuns = new HashSet<>();
		mOld = old;
		mNew = newConjunct;

		final ImmutableList<IPredicate> oldConjuncts;
		if (old instanceof PredicateWithConjuncts) {
			oldConjuncts = ((PredicateWithConjuncts) old).mConjuncts;
		} else {
			oldConjuncts = ImmutableList.singleton(old);
		}
		mConjuncts = new ImmutableList<>(newConjunct, oldConjuncts);
	}

	public ImmutableList<IPredicate> getConjuncts() {
		return mConjuncts;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, mSerial);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() == obj.getClass()) {
			final PredicateWithConjuncts other = (PredicateWithConjuncts) obj;
			return mSerial == other.mSerial;
		}
		return false;
	}

	@Override
	public Term getFormula() {
		// compute on-demand (and possibly use partial results when constructed from conjunction)
		if (mFormula == null) {
			if (mOld != null) {
				mFormula = SmtUtils.and(mScript, mOld.getFormula(), mNew.getFormula());
			} else {
				Term term = null;
				for (final IPredicate conjunct : mConjuncts) {
					if (term == null) {
						term = conjunct.getFormula();
					} else {
						term = SmtUtils.and(mScript, term, conjunct.getFormula());
					}
				}
				mFormula = term;
			}
		}
		return mFormula;
	}

	@Override
	public Term getClosedFormula() {
		// compute on-demand (and possibly use partial results when constructed from conjunction)
		if (mClosedFormula == null) {
			if (mOld != null) {
				mClosedFormula = SmtUtils.and(mScript, mOld.getClosedFormula(), mNew.getClosedFormula());
			} else {
				Term term = null;
				for (final IPredicate conjunct : mConjuncts) {
					if (term == null) {
						term = conjunct.getClosedFormula();
					} else {
						term = SmtUtils.and(mScript, term, conjunct.getClosedFormula());
					}
				}
				mClosedFormula = term;
			}
		}
		return mClosedFormula;
	}

	@Override
	public Set<IProgramVar> getVars() {
		// compute on-demand (and possibly use partial results when constructed from conjunction)
		if (mVars.isEmpty()) {
			if (mOld != null) {
				mVars.addAll(mOld.getVars());
				mVars.addAll(mNew.getVars());
			} else {
				for (final IPredicate conjunct : mConjuncts) {
					mVars.addAll(conjunct.getVars());
				}
			}
		}
		return mVars;
	}

	@Override
	public Set<IProgramFunction> getFuns() {
		// compute on-demand (and possibly use partial results when constructed from conjunction)
		if (mFuns.isEmpty()) {
			if (mOld != null) {
				mFuns.addAll(mOld.getFuns());
				mFuns.addAll(mNew.getFuns());
			} else {
				for (final IPredicate conjunct : mConjuncts) {
					mFuns.addAll(conjunct.getFuns());
				}
			}
		}
		return mFuns;
	}

	@Override
	public String toString() {
		return mSerial + "#" + mConjuncts.toString();
	}
}
