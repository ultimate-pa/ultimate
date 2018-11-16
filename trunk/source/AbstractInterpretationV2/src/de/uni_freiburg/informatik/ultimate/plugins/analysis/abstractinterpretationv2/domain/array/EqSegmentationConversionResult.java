package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class EqSegmentationConversionResult<STATE extends IAbstractState<STATE>> {
	private final ArrayDomainState<STATE> mFirstState;
	private final ArrayDomainState<STATE> mSecondState;
	private final Segmentation mSegmentation;
	private final Map<IProgramVar, Segmentation> mNewSegmentations;

	public EqSegmentationConversionResult(final ArrayDomainState<STATE> firstState,
			final ArrayDomainState<STATE> secondState, final Segmentation segmentation,
			final Map<IProgramVar, Segmentation> newSegmentations) {
		mFirstState = firstState;
		mSecondState = secondState;
		mSegmentation = segmentation;
		mNewSegmentations = newSegmentations;
	}

	public ArrayDomainState<STATE> getFirstState() {
		return mFirstState;
	}

	public ArrayDomainState<STATE> getSecondState() {
		return mSecondState;
	}

	public Segmentation getSegmentation() {
		return mSegmentation;
	}

	public Map<IProgramVar, Segmentation> getNewSegmentations() {
		return mNewSegmentations;
	}
}
