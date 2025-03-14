package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;

public class BooleanDomain implements Domain<BooleanDomain> {
	public final boolean canBeTrue, canBeFalse;

	public BooleanDomain(final boolean mCanBeTrue, final boolean mCanBeFalse) {
		canBeTrue = mCanBeTrue;
		canBeFalse = mCanBeFalse;
	}

	public BooleanDomain and(final BooleanDomain b) {
		final boolean mCanBeTrue = canBeTrue && b.canBeTrue;
		final boolean mCanBeFalse = canBeFalse || b.canBeFalse;
		return new BooleanDomain(mCanBeTrue, mCanBeFalse);
	}

	public BooleanDomain or(final BooleanDomain b) {
		final boolean mCanBeTrue = canBeTrue || b.canBeTrue;
		final boolean mCanBeFalse = canBeFalse && b.canBeFalse;
		return new BooleanDomain(mCanBeTrue, mCanBeFalse);
	}

	public BooleanDomain xor(final BooleanDomain b) {
		final boolean mCanBeTrue = (canBeTrue && b.canBeFalse) || (canBeFalse && b.canBeTrue);
		final boolean mCanBeFalse = (canBeTrue && b.canBeTrue) || (canBeFalse && b.canBeFalse);
		return new BooleanDomain(mCanBeTrue, mCanBeFalse);
	}

	public BooleanDomain not() {
		return new BooleanDomain(canBeFalse, canBeTrue);
	}

	@Override
	public BooleanDomain union(final BooleanDomain domain) {
		final boolean mCanBeTrue = canBeTrue || domain.canBeTrue;
		final boolean mCanBeFalse = canBeFalse || domain.canBeFalse;
		return new BooleanDomain(mCanBeTrue, mCanBeFalse);
	}

	@Override
	public BooleanDomain intersection(final BooleanDomain domain) {
		final boolean mCanBeTrue = canBeTrue && domain.canBeTrue;
		final boolean mCanBeFalse = canBeFalse && domain.canBeFalse;
		return new BooleanDomain(mCanBeTrue, mCanBeFalse);
	}

	@Override
	public BooleanDomain difference(final BooleanDomain domain) {
		final boolean mCanBeTrue = canBeTrue ^ domain.canBeTrue;
		final boolean mCanBeFalse = canBeFalse ^ domain.canBeFalse;
		return new BooleanDomain(mCanBeTrue, mCanBeFalse);
	}

	/**
	 * Returns the {@link BooleanDomain} that can be true if this domain can be true and the other domain can be false,
	 * vice versa for being false
	 */
	@Override
	public BooleanDomain complement(final BooleanDomain domain) {
		final boolean mCanBeTrue = canBeTrue && domain.canBeFalse;
		final boolean mCanBeFalse = canBeFalse && domain.canBeTrue;
		return new BooleanDomain(mCanBeTrue, mCanBeFalse);
	}

	@Override
	public boolean contains(final Domain<?> domain) {
		if (!(domain instanceof BooleanDomain)) {
			return false;
		}
		final BooleanDomain domainCast = (BooleanDomain) domain;
		if ((canBeTrue ^ domainCast.canBeTrue) || (canBeFalse ^ domainCast.canBeFalse)) {
			// one can be true / false, but the other can't
			return false;
		}
		return false;
	}

	@Override
	public boolean isEmpty() {
		return !canBeTrue && !canBeFalse;
	}

	@Override
	public ArrayList<Boolean> getValues() {
		final ArrayList<Boolean> bools = new ArrayList<>();
		if (canBeTrue) {
			bools.add(true);
		}
		if (canBeFalse) {
			bools.add(false);
		}
		return bools;
	}

	@Override
	public ReturnType getType() {
		return ReturnType.Boolean;
	}

	@Override
	public String toString() {
		return "{" + (canBeTrue ? "true" : "") + (canBeTrue && canBeFalse ? ", " : "") + (canBeFalse ? "false" : "")
				+ "}";
	}

	@Override
	public BooleanDomain getFullDomain() {
		return new BooleanDomain(true, true);
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof BooleanDomain)) {
			return false;
		}
		final BooleanDomain bCast = (BooleanDomain) b;
		return canBeTrue == bCast.canBeTrue && canBeFalse == bCast.canBeFalse;
	}

	@Override
	public BooleanDomain domainFrom(final Object singleValue) {
		if (((boolean) singleValue)) {
			return new BooleanDomain(true, false);
		}
		return new BooleanDomain(false, true);
	}
}