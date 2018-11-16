package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

class EqSegmentationConversionResult {
	private final Segmentation mSegmentation;
	private final Map<IProgramVar, Segmentation> mNewSegmentations;
	private final Collection<Term> mConstraints;
	private final Collection<IProgramVarOrConst> mNewVariables;
	private final Collection<IProgramVarOrConst> mRemoveVariablesFirstState;
	private final Collection<IProgramVarOrConst> mRemoveVariablesSecondState;

	public EqSegmentationConversionResult(final Segmentation segmentation,
			final Map<IProgramVar, Segmentation> newSegmentations, final Collection<Term> constraints,
			final Collection<IProgramVarOrConst> newVariables,
			final Collection<IProgramVarOrConst> removeVariablesFirstState,
			final Collection<IProgramVarOrConst> removeVariablesSecondState) {
		mSegmentation = segmentation;
		mNewSegmentations = newSegmentations;
		mConstraints = constraints;
		mNewVariables = newVariables;
		mRemoveVariablesFirstState = removeVariablesFirstState;
		mRemoveVariablesSecondState = removeVariablesSecondState;
	}

	public Segmentation getSegmentation() {
		return mSegmentation;
	}

	public Map<IProgramVar, Segmentation> getNewSegmentations() {
		return mNewSegmentations;
	}

	public Collection<Term> getConstraints() {
		return mConstraints;
	}

	public Collection<IProgramVarOrConst> getNewVariables() {
		return mNewVariables;
	}

	public Collection<IProgramVarOrConst> getRemoveVariablesFirstState() {
		return mRemoveVariablesFirstState;
	}

	public Collection<IProgramVarOrConst> getRemoveVariablesSecondState() {
		return mRemoveVariablesSecondState;
	}
}
