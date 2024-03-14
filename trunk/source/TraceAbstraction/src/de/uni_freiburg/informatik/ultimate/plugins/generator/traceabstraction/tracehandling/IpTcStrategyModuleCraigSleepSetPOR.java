/*
 * Copyright (C) 2024 Marcel Ebbinghaus
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;

/**
 * Variant of IpTcStrategyModuleCraig for POR with sleep sets.
 * 
 * @author Marcel Ebbinghaus
 * 
 * @param <LETTER>
 *         The type of letters.
 */
public abstract class IpTcStrategyModuleCraigSleepSetPOR<LETTER extends IIcfgTransition<?>>
extends IpTcStrategyModuleTraceCheck<InterpolatingTraceCheckCraig<LETTER>, LETTER> {

/**
 * Constructor.
 *
 * @author Marcel Ebbinghaus
 *
 * @param taskIdentifier
 *            taskIdentifier.
 * @param services
 *            Ultimate services.  
 * @param prefs
 *            Ultimate preferences.   
 * @param counterExample
 *            counter example.            
 * @param precondition
 *            precondition.            
 * @param postcondition
 *            postcondition.            
 * @param assertionOrderModulation
 *            assertionOrderModulation.               
 * @param predicateUnifier
 *            predicate unifier.            
 * @param predicateFactory
 *            factory.                           
 */
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
		TraceCheckUtils.getSequenceOfProgramPointsWithSleepSet(mCounterexample.getStateSequence()), mServices,
		mPrefs.getCfgSmtToolkit(), managedScript, mPredicateFactory, mPredicateUnifier, assertionOrder,
		mPrefs.computeCounterexample(), mPrefs.collectInterpolantStatistics(), interpolationTechnique,
		instanticateArrayExt, xnfConversionTechnique, simplificationTechnique,
		innerRecursiveNestedInterpolationCall);
}

protected abstract ManagedScript constructManagedScript();

protected abstract InterpolationTechnique getInterpolationTechnique();
}
