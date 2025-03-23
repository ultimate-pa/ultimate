package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;

public class BitVectorDomain implements Domain<BitVectorDomain> {
	private final int mLength;

	public BitVectorDomain(final int length) {
		mLength = length;
	}

	@Override
	public BitVectorDomain union(final Domain<?> domain) {
		if (!(domain instanceof BitVectorDomain)) {
			return null;
		}
		final BitVectorDomain castDomain = (BitVectorDomain) domain;
		if (castDomain.mLength != mLength) {
			return null;
		}

		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BitVectorDomain intersection(final Domain<?> domain) {
		if (!(domain instanceof BitVectorDomain)) {
			return null;
		}
		final BitVectorDomain castDomain = (BitVectorDomain) domain;
		if (castDomain.mLength != mLength) {
			return null;
		}

		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BitVectorDomain difference(final Domain<?> domain) {
		if (!(domain instanceof BitVectorDomain)) {
			return null;
		}
		final BitVectorDomain castDomain = (BitVectorDomain) domain;
		if (castDomain.mLength != mLength) {
			return null;
		}

		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean contains(final Domain<?> domain) {
		if (!(domain instanceof BitVectorDomain)) {
			return false;
		}
		final BitVectorDomain castDomain = (BitVectorDomain) domain;
		if (castDomain.mLength != mLength) {
			return false;
		}

		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isEmpty() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public long getValueCount() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public ArrayList<? extends Object> getValues() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ReturnType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BitVectorDomain getFullDomain() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public BitVectorDomain domainFrom(final Object singleValue) {
		// TODO Auto-generated method stub
		return null;
	}

	public static BitVectorDomain getDomain(final Sort sort) {
		assert sort.isBitVecSort();
		final int length = Integer.parseInt(sort.getIndices()[0]);
		return new BitVectorDomain(length);
	}

}
