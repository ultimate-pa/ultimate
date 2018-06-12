package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.AbstractTemplateIncreasingDimensionsStrategy;

public class InvariantSynthesisSettings {
	
	// The settings for the theorem solver, that is used for invariant synthesis.
	SolverSettings mSolverSettings;
	private final boolean mUseNonlinearConstraints;
	private final boolean mUseUnsatCores;
	private final boolean mUseAbstractInterpretationPredicates;
	private final boolean mUseWPForPathInvariants;
	private final boolean mUseLBE; // use large-block encoding?
	private final AbstractTemplateIncreasingDimensionsStrategy mTemplateDimensionsStrat;
	
	public InvariantSynthesisSettings(SolverSettings solverSettings, final AbstractTemplateIncreasingDimensionsStrategy templateDimensionsStrat, 
			final boolean useNonlinearConstraints, 	final boolean useUnsatCores, 
			final boolean useAbstractInterpretationPredicates, final boolean useWPForPathInvariants, final boolean useLBE) {
		mUseNonlinearConstraints = useNonlinearConstraints;
		mSolverSettings = solverSettings;
		mUseUnsatCores = useUnsatCores;
		mUseAbstractInterpretationPredicates = useAbstractInterpretationPredicates;
		mUseWPForPathInvariants = useWPForPathInvariants;
		mTemplateDimensionsStrat = templateDimensionsStrat;
		mUseLBE = useLBE;
	}
	
	public InvariantSynthesisSettings(SolverSettings solverSettings, final boolean useNonlinearConstraints,
			final boolean useUnsatCores, final boolean useAbstractInterpretationPredicates, final boolean useWPForPathInvariants, final boolean useLBE) {
		mUseNonlinearConstraints = useNonlinearConstraints;
		mSolverSettings = solverSettings;
		mUseUnsatCores = useUnsatCores;
		mUseAbstractInterpretationPredicates = useAbstractInterpretationPredicates;
		mUseWPForPathInvariants = useWPForPathInvariants;
		mTemplateDimensionsStrat = null;
		mUseLBE = useLBE;
	}
	
	public final boolean useNonLinearConstraints() {
		return mUseNonlinearConstraints;
	}
	
	public final boolean useUnsatCores() {
		return mUseUnsatCores;
	}
	
	public final boolean useAbstractInterpretation() {
		return mUseAbstractInterpretationPredicates;
	}
	
	public final boolean useWeakestPrecondition() {
		return mUseWPForPathInvariants;
	}
	
	public final SolverSettings getSolverSettings() {
		return mSolverSettings;
	}
	
	public final boolean useLargeBlockEncoding() {
		return mUseLBE;
	}
	
	public final AbstractTemplateIncreasingDimensionsStrategy getTemplateDimensionsStrategy() {
		return mTemplateDimensionsStrat;
	}
	
}
