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

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * A signature is a tuple of an opaque identifier and a non-empty array of {@link CCParameter}s (a CCTerm together with
 * a constant offset). It is used as the key for the global signature-to-trigger map in CClosure. Hash and equality are
 * based on each parameter's <em>representative</em> and its <em>offset to that representative</em>, so when
 * representatives or offsets change (e.g. after a merge), the same parameter array yields a different signature key.
 *
 * @author Jochen Hoenicke
 */
public class SignatureTrigger extends SimpleListable<SignatureTrigger> {

	private final Object mId;
	/**
	 * The arguments of the signature as {@link CCParameter}s: argument {@code i} has value
	 * {@code mParams[i].getCCTerm() + mParams[i].getOffset()}. Offset-free arguments are bare {@link CCTerm}s, which
	 * keeps plain congruence closure free of any offset cost. The effective offset that the signature is keyed on is
	 * {@code mParams[i].getOffsetToRep()} (the parameter's offset relative to its representative; see
	 * {@link #effectiveOffset(int)}), so two applications are congruent only if their arguments have the same
	 * representative <em>and</em> the same effective offset.
	 */
	private final CCParameter[] mParams;
	private int mLastHashCode;

	private SignatureTrigger mMergedTrigger;
	private SignatureBackRef[] mBackrefs;

	/**
	 * Create a signature with the given identifier and non-empty parameter array.
	 *
	 * @param id
	 *            opaque identifier (e.g. function symbol for congruence, or trigger id for reverse triggers).
	 * @param params
	 *            non-empty array of {@link CCParameter}s (bare {@link CCTerm}s for offset-free arguments).
	 */
	public SignatureTrigger(final Object id, final CCParameter[] params) {
		mId = id;
		mParams = params;
		mLastHashCode = computeHashCode();
	}

	/**
	 * The effective offset of argument {@code index}: the parameter's offset relative to its representative. This is
	 * what determines, together with the representative, whether two signatures are congruent.
	 */
	private Rational effectiveOffset(final int index) {
		return mParams[index].getOffsetToRep();
	}

	public Object getId() {
		return mId;
	}

	/** Returns the number of arguments in this signature. */
	public int getTermCount() {
		return mParams.length;
	}

	/** Returns the argument at the given index. */
	public CCParameter getParam(final int index) {
		return mParams[index];
	}

	public void rehash(CClosure engine, int argPosition, CCTerm oldRep, CCTerm newRep, Rational offsetDelta) {
		/* only if not merged */
		if (mMergedTrigger == null) {
			assert mBackrefs != null;
			if (!inList()) {
				assert mLastHashCode == computeHashCode();
				engine.moveToSignatureTodo(this);
			}
			recomputeHashCode(argPosition, oldRep, newRep, offsetDelta);
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
		for (int i = 0; i < mParams.length; i++) {
			// Use disjoint salts (2*i for the representative, 2*i+1 for the offset) so the two contributions do not
			// trivially cancel against each other.
			h ^= HashUtils.hashJenkins(2 * i, mParams[i].getRepresentative());
			h ^= HashUtils.hashJenkins(2 * i + 1, effectiveOffset(i).hashCode());
		}
		return h;
	}

	/**
	 * Incrementally update the cached hash when argument {@code argPos}'s representative changes from {@code oldRep} to
	 * {@code newRep} and its offset to the representative changes by {@code offsetDelta}. This must be called before the
	 * term's {@code mOffsetToRep} is actually updated, so {@link #effectiveOffset(int)} still reflects the old value.
	 */
	public void recomputeHashCode(int argPos, CCTerm oldRep, CCTerm newRep, Rational offsetDelta) {
		final int hOldRep = HashUtils.hashJenkins(2 * argPos, oldRep.hashCode());
		final int hNewRep = HashUtils.hashJenkins(2 * argPos, newRep.hashCode());
		mLastHashCode ^= hOldRep ^ hNewRep;
		if (!offsetDelta.equals(Rational.ZERO)) {
			final Rational oldEff = effectiveOffset(argPos);
			final Rational newEff = oldEff.add(offsetDelta);
			final int hOldOff = HashUtils.hashJenkins(2 * argPos + 1, oldEff.hashCode());
			final int hNewOff = HashUtils.hashJenkins(2 * argPos + 1, newEff.hashCode());
			mLastHashCode ^= hOldOff ^ hNewOff;
		}
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
		if (!mId.equals(other.mId) || mParams.length != other.mParams.length) {
			return false;
		}
		for (int i = 0; i < mParams.length; i++) {
			if (!mParams[i].sameValueAs(other.mParams[i])) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder("Sig[").append(mId);
		for (final CCParameter p : mParams) {
			sb.append(',').append(p);
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
		mBackrefs = new SignatureBackRef[mParams.length];
		for (int i = 0; i < mParams.length; i++) {
			mBackrefs[i] = new SignatureBackRef(this, i);
			cclosure.addSignatureBackRef(mParams[i].getCCTerm(), mBackrefs[i]);
		}
	}

	public void removeBackrefs(CClosure cclosure) {
		for (int i = 0; i < mParams.length; i++) {
			cclosure.removeSignatureBackRef(mParams[i].getCCTerm(), mBackrefs[i]);
		}
		mBackrefs = null;
	}
}
