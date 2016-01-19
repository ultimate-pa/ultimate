package de.uni_freiburg.informatik.ultimate.result;

/**
 * Use this if you do not want to implement a backtranslation provider.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <TTE>
 * @param <TE>
 */
public class NoBacktranslationValueProvider<TTE, TE> implements IBacktranslationValueProvider<TTE, TE> {

	@Override
	public int getStartLineNumberFromStep(TTE step) {
		throw new UnsupportedOperationException("NoBacktranslationValueProvider");
	}

	@Override
	public int getEndLineNumberFromStep(TTE step) {
		throw new UnsupportedOperationException("NoBacktranslationValueProvider");
	}

	@Override
	public String getFileNameFromStep(TTE step) {
		throw new UnsupportedOperationException("NoBacktranslationValueProvider");
	}

	@Override
	public String getStringFromStep(TTE step) {
		throw new UnsupportedOperationException("NoBacktranslationValueProvider");
	}

	@Override
	public String getStringFromTraceElement(TTE traceelement) {
		throw new UnsupportedOperationException("NoBacktranslationValueProvider");
	}

	@Override
	public String getStringFromExpression(TE expression) {
		throw new UnsupportedOperationException("NoBacktranslationValueProvider");
	}

}
