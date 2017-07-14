package de.uni_freiburg.informatik.ultimate.core.model.translation;

import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

/**
 * Provides various values for the generic types used during backtranslation.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 *
 * @see {@link IBacktranslationService}
 * @see {@link ITranslator}
 *
 * @param <TTE>
 * @param <TE>
 */
public interface IBacktranslationValueProvider<TTE, TE> {

	int getStartLineNumberFromStep(TTE step);

	int getEndLineNumberFromStep(TTE step);

	String getOriginFileNameFromStep(TTE step);

	String getFileNameFromStep(TTE step);

	String getStringFromStep(TTE step);

	String getStringFromTraceElement(TTE traceelement);

	String getStringFromExpression(TE expression);

}