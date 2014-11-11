package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;

/**
 * Result that reports that a counter example for an LTL property was found and
 * that it is finite.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class LTLFiniteCounterExampleResult<ELEM extends IElement, TE extends IElement, E> extends
		CounterExampleResult<ELEM, TE, E> {

	public LTLFiniteCounterExampleResult(ELEM position, String plugin, IBacktranslationService translatorSequence,
			IProgramExecution<TE, E> pe, Check  check) {
		super(annotatePositionWithCheck(position, check), plugin, translatorSequence, pe);
	}

	private static <ELEM extends IElement> ELEM annotatePositionWithCheck(ELEM position, Check check) {
		if (check == null || !check.getSpec().equals(Spec.LTL)) {
			throw new IllegalArgumentException("You cannot use " + LTLFiniteCounterExampleResult.class.getSimpleName()
					+ " for specs different from LTL");
		}
		position.getPayload().getAnnotations().put(Check.getIdentifier(), check);
		return position;
	}
}
