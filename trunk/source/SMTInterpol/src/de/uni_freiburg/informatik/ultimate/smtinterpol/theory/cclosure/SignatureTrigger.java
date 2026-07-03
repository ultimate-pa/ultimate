/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * A signature is a tuple of an opaque identifier and a non-empty array of CCTerms. It is used as the key for the
 * global signature-to-trigger map in CClosure. Hash and equality are based on the <em>representatives</em> of the
 * terms, so when representatives change (e.g. after a merge), the same term array yields a different signature key.
 *
 * @author Jochen Hoenicke
 */
public class SignatureTrigger extends SimpleListable<SignatureTrigger> {

	private final Object mId;
	private final CCTerm[] mTerms;
	private int mLastHashCode;

	private SignatureTrigger mMergedTrigger;
	private SignatureBackRef[] mBackrefs;
	/**
	 * Create a signature with the given identifier and non-empty term array. The array may contain any CCTerms, not
	 * necessarily representatives. The array is copied defensively.
	 *
	 * @param id
	 *            opaque identifier (e.g. function symbol for congruence, or trigger id for reverse triggers).
	 * @param terms
	 *            non-empty array of CCTerms.
	 */
	public SignatureTrigger(final Object id, final CCTerm[] terms) {
		mId = id;
		mTerms = terms;
		mLastHashCode = computeHashCode();
	}

	public Object getId() {
		return mId;
	}

	/** Returns the number of terms in this signature. */
	public int getTermCount() {
		return mTerms.length;
	}

	/** Returns the term at the given index. */
	public CCTerm getTerm(final int index) {
		return mTerms[index];
	}

	/** Returns an unmodifiable list view of the terms. */
	public List<CCTerm> getTerms() {
		return Arrays.asList(mTerms);
	}

	public void rehash(CClosure engine, int argPosition, CCTerm oldRep, CCTerm newRep) {
		/* only if not merged */
		if (mMergedTrigger == null) {
			assert mBackrefs != null;
			if (!inList()) {
				assert mLastHashCode == computeHashCode();
				engine.moveToSignatureTodo(this);
			}
			recomputeHashCode(argPosition, oldRep, newRep);
		}
	}

	/**
	 * Merge this trigger with another. Called by CClosure.addSignature when a Trigger with the same signature already exists.
	 * This combines the information of the two triggers into a single trigger, and may also trigger actions like adding pending congruences or activating reverse triggers.
	 * @param engine the congruence closure engine.
	 * @param other the trigger that was merged into this trigger.
	 */
	public void merge(CClosure engine, SignatureTrigger other) {
		assert this != other;
		// System.err.println("MERGE " + this + " with " + other);
		assert other.mMergedTrigger == null;
		other.mMergedTrigger = this;
	}

	/**
	 * Undo the merge of this trigger with another. Called when undoing a merge at checkpoint.
	 * @param engine
	 *            the congruence closure engine.
	 * @param other
	 *            the trigger that was merged into this trigger.
	 */
	public void undoMerge(CClosure engine, SignatureTrigger other) {
		// System.err.println("UNDO MERGE " + this + " with " + other);
		assert other.mMergedTrigger == this;
		other.mMergedTrigger = null;
	}

	@Override
	public int hashCode() {
		assert computeHashCode() == mLastHashCode;
		return mLastHashCode;
	}

	public int computeHashCode() {
		int h = mId.hashCode();
		for (int i = 0; i < mTerms.length; i++) {
			h ^= HashUtils.hashJenkins(i, mTerms[i].getRepresentative());
		}
		return h;
	}

	public void recomputeHashCode(int argPos, CCTerm oldRep, CCTerm newRep) {
		final int hOld = HashUtils.hashJenkins(argPos, oldRep.hashCode());
		final int hNew = HashUtils.hashJenkins(argPos, newRep.hashCode());
		// assert computeHashCode() == (mLastHashCode ^ hOld ^ hNew);
		mLastHashCode ^= hOld ^ hNew;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof SignatureTrigger)) {
			return false;
		}
		final SignatureTrigger other = (SignatureTrigger) obj;
		if (!mId.equals(other.mId) || mTerms.length != other.mTerms.length) {
			return false;
		}
		for (int i = 0; i < mTerms.length; i++) {
			if (mTerms[i].getRepresentative() != other.mTerms[i].getRepresentative()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("Sig[").append(mId);
		for (final CCTerm t : mTerms) {
			sb.append(',').append(t);
		}
		return sb.append(']').toString();
	}

	public boolean unmerge(CClosure cclosure) {
		if (mMergedTrigger != null) {
			mMergedTrigger.undoMerge(cclosure, this);
			return true;
		}
		return false;
	}

	public void addBackrefs(CClosure cclosure) {
		mBackrefs = new SignatureBackRef[mTerms.length];
		for (int i = 0; i < mTerms.length; i++) {
			mBackrefs[i] = new SignatureBackRef(this, i);
			cclosure.addSignatureBackRef(mTerms[i], mBackrefs[i]);
		}
	}

	public void removeBackrefs(CClosure cclosure) {
		for (int i = 0; i < mTerms.length; i++) {
			cclosure.removeSignatureBackRef(mTerms[i], mBackrefs[i]);
		}
		mBackrefs = null;
	}
}
