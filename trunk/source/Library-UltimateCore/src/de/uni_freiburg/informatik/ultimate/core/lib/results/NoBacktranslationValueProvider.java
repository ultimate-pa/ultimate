package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.core.model.translation.IBacktranslationValueProvider;

/**
 * Use this if you do not want to implement a backtranslation provider.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <TTE>
 * @param <TE>
 */
public class NoBacktranslationValueProvider<TTE, TE> implements IBacktranslationValueProvider<TTE, TE> {

	private static final String NO_BACKTRANSLATION_VALUE_PROVIDER = "NoBacktranslationValueProvider";

	@Override
	public int getStartLineNumberFromStep(final TTE step) {
		throw new UnsupportedOperationException(NO_BACKTRANSLATION_VALUE_PROVIDER);
	}

	@Override
	public int getEndLineNumberFromStep(final TTE step) {
		throw new UnsupportedOperationException(NO_BACKTRANSLATION_VALUE_PROVIDER);
	}

	@Override
	public String getFileNameFromStep(final TTE step) {
		throw new UnsupportedOperationException(NO_BACKTRANSLATION_VALUE_PROVIDER);
	}

	@Override
	public String getStringFromStep(final TTE step) {
		throw new UnsupportedOperationException(NO_BACKTRANSLATION_VALUE_PROVIDER);
	}

	@Override
	public String getStringFromTraceElement(final TTE traceelement) {
		throw new UnsupportedOperationException(NO_BACKTRANSLATION_VALUE_PROVIDER);
	}

	@Override
	public String getStringFromExpression(final TE expression) {
		throw new UnsupportedOperationException(NO_BACKTRANSLATION_VALUE_PROVIDER);
	}

	@Override
	public String getOriginFileNameFromStep(final TTE step) {
		throw new UnsupportedOperationException(NO_BACKTRANSLATION_VALUE_PROVIDER);
	}

}
