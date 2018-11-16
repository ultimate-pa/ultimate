package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

class UnificationResult<STATE extends IAbstractState<STATE>> {
	private final ArrayDomainState<STATE> mFirstState;
	private final ArrayDomainState<STATE> mSecondState;
	private final EqClassSegmentation mSegmentation;
	private Map<IProgramVar, EqClassSegmentation> mAuxVarSegmentations;

	public UnificationResult(final ArrayDomainState<STATE> firstState, final ArrayDomainState<STATE> secondState,
			final EqClassSegmentation segmentation, final Map<IProgramVar, EqClassSegmentation> auxVarSegmentations) {
		mFirstState = firstState;
		mSecondState = secondState;
		mSegmentation = segmentation;
		mAuxVarSegmentations = auxVarSegmentations;
	}

	public Map<IProgramVar, EqClassSegmentation> getAuxVarSegmentations() {
		return mAuxVarSegmentations;
	}

	public void setAuxVarSegmentations(final Map<IProgramVar, EqClassSegmentation> auxVarSegmentations) {
		mAuxVarSegmentations = auxVarSegmentations;
	}

	public ArrayDomainState<STATE> getFirstState() {
		return mFirstState;
	}

	public ArrayDomainState<STATE> getSecondState() {
		return mSecondState;
	}

	public EqClassSegmentation getSegmentation() {
		return mSegmentation;
	}

	public List<Set<Term>> getBounds() {
		return mSegmentation.getBounds();
	}

	public List<IProgramVar> getFirstValues() {
		return mSegmentation.getFirstValues();
	}

	public List<IProgramVar> getSecondValues() {
		return mSegmentation.getSecondValues();
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append("States:\n");
		stringBuilder.append(mFirstState).append('\n');
		stringBuilder.append(mSecondState).append("\n\n");
		stringBuilder.append("Segmentation: ").append(mSegmentation).append('\n');
		stringBuilder.append("AuxVarSegmentations: ").append(mAuxVarSegmentations).append('\n');
		return stringBuilder.toString();
	}
}
