package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolatingTraceCheckCraig;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;

public abstract class IpTcStrategyModuleCraigSleepSetPOR<LETTER extends IIcfgTransition<?>>
extends IpTcStrategyModuleTraceCheck<InterpolatingTraceCheckCraig<LETTER>, LETTER> {

public IpTcStrategyModuleCraigSleepSetPOR(final TaskIdentifier taskIdentifier, final IUltimateServiceProvider services,
	final TaCheckAndRefinementPreferences<LETTER> prefs, final IRun<LETTER, ?> counterExample,
	final IPredicate precondition, final IPredicate postcondition,
	final AssertionOrderModulation<LETTER> assertionOrderModulation, final IPredicateUnifier predicateUnifier,
	final PredicateFactory predicateFactory) {
super(taskIdentifier, services, prefs, counterExample, precondition, postcondition, assertionOrderModulation,
		predicateUnifier, predicateFactory);
}

@Override
protected InterpolatingTraceCheckCraig<LETTER> construct() {
final InterpolationTechnique interpolationTechnique = getInterpolationTechnique();
assert interpolationTechnique == InterpolationTechnique.Craig_NestedInterpolation
		|| interpolationTechnique == InterpolationTechnique.Craig_TreeInterpolation;

final AssertCodeBlockOrder assertionOrder =
		mAssertionOrderModulation.get(mCounterexample, interpolationTechnique);
final XnfConversionTechnique xnfConversionTechnique = mPrefs.getXnfConversionTechnique();
final SimplificationTechnique simplificationTechnique = mPrefs.getSimplificationTechnique();
final ManagedScript managedScript = constructManagedScript();

final boolean instanticateArrayExt = true;
final boolean innerRecursiveNestedInterpolationCall = false;
return new InterpolatingTraceCheckCraig<>(mPrecondition, mPostcondition, new TreeMap<Integer, IPredicate>(),
		NestedWord.nestedWord(mCounterexample.getWord()),
		mCounterexample.getStateSequence(), mServices,
		mPrefs.getCfgSmtToolkit(), managedScript, mPredicateFactory, mPredicateUnifier, assertionOrder,
		mPrefs.computeCounterexample(), mPrefs.collectInterpolantStatistics(), interpolationTechnique,
		instanticateArrayExt, xnfConversionTechnique, simplificationTechnique,
		innerRecursiveNestedInterpolationCall);
}

protected abstract ManagedScript constructManagedScript();

protected abstract InterpolationTechnique getInterpolationTechnique();
}
