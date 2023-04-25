package de.uni_freiburg.informatik.ultimate.automata.rabin;

/**
 * example class for computing RGB states for Integer data type.
 */
public class RGBIntFactory implements IRedGreenBlueStateFactory<Integer> {

	final int mBASE = 3;

	@Override
	public Integer getRedContent(final Integer content) {

		return content * mBASE;
	}

	@Override
	public Integer getGreenContent(final Integer content) {

		return (content * mBASE) - 1;
	}

	@Override
	public Integer getBlueContent(final Integer content) {

		return (content * mBASE) - 2;
	}

	@Override
	public Integer getOriginal(final Integer content) {

		return Math.floorDiv(content, mBASE);
	}

}
