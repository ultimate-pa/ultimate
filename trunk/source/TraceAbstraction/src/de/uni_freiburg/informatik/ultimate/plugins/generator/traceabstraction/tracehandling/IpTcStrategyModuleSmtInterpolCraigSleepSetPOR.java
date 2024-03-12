package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;

public class IpTcStrategyModuleSmtInterpolCraigSleepSetPOR<LETTER extends IIcfgTransition<?>>
extends IpTcStrategyModuleCraigSleepSetPOR<LETTER> {

private static final InterpolationTechnique[] SUPPORTED_TECHNIQUES = new InterpolationTechnique[] {
	InterpolationTechnique.Craig_NestedInterpolation, InterpolationTechnique.Craig_TreeInterpolation, };

private final long mTimeoutInMillis;
private final InterpolationTechnique mInterpolationTechnique;

public IpTcStrategyModuleSmtInterpolCraigSleepSetPOR(final TaskIdentifier taskIdentifier,
	final IUltimateServiceProvider services, final TaCheckAndRefinementPreferences<LETTER> prefs,
	final IRun<LETTER, ?> counterExample, final IPredicate precondition, final IPredicate postcondition,
	final AssertionOrderModulation<LETTER> assertionOrderModulation, final IPredicateUnifier predicateUnifier,
	final PredicateFactory predicateFactory, final long timeoutInMillis,
	final InterpolationTechnique interpolationTechnique) {
super(taskIdentifier, services, prefs, counterExample, precondition, postcondition, assertionOrderModulation,
		predicateUnifier, predicateFactory);
mTimeoutInMillis = timeoutInMillis;
mInterpolationTechnique = interpolationTechnique;
assert Arrays.stream(SUPPORTED_TECHNIQUES).anyMatch(
		a -> a == mInterpolationTechnique) : "Unsupported interpolation technique " + mInterpolationTechnique;
}

@Override
protected ManagedScript constructManagedScript() {
final long timeout = computeTimeout(mTimeoutInMillis);
final SolverMode solverMode = SolverMode.Internal_SMTInterpol;

final SolverSettings solverSettings = mPrefs.constructSolverSettings(mTaskIdentifier).setSolverMode(solverMode)
		.setSmtInterpolTimeout(timeout);
return createExternalManagedScript(solverSettings);
}

@Override
protected final InterpolationTechnique getInterpolationTechnique() {
return mInterpolationTechnique;
}
}