/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.IRunningTaskStackProvider;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.CegarLoopForPetriNet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.FloydHoareAutomataReuse;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.LanguageOperation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class CegarLoopResult<L extends IIcfgTransition<?>> {

	private static final boolean EXTENDED_HOARE_ANNOTATION_LOGGING = true;

	private final Result mOverallResult;
	private final IProgramExecution<L, Term> mProgramExecution;
	private final List<UnprovabilityReason> mUnprovabilityReasons;
	private final IRunningTaskStackProvider mRunningTaskStackProvider;
	private final IStatisticsDataProvider mCegarLoopStatisticsGenerator;
	private final IElement mArtifact;
	private final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> mFloydHoareAutomata;

	public CegarLoopResult(final Result overallResult, final IProgramExecution<L, Term> programExecution,
			final List<UnprovabilityReason> unprovabilityReasons,
			final IRunningTaskStackProvider runningTaskStackProvider,
			final IStatisticsDataProvider cegarLoopStatisticsGenerator, final IElement artifact,
			final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> floydHoareAutomata) {
		super();
		mOverallResult = overallResult;
		mProgramExecution = programExecution;
		mUnprovabilityReasons = unprovabilityReasons;
		mRunningTaskStackProvider = runningTaskStackProvider;
		mCegarLoopStatisticsGenerator = cegarLoopStatisticsGenerator;
		mArtifact = artifact;
		mFloydHoareAutomata = floydHoareAutomata;
	}

	public Result getOverallResult() {
		return mOverallResult;
	}

	public IProgramExecution<L, Term> getProgramExecution() {
		return mProgramExecution;
	}

	public List<UnprovabilityReason> getUnprovabilityReasons() {
		return mUnprovabilityReasons;
	}

	public IRunningTaskStackProvider getRunningTaskStackProvider() {
		return mRunningTaskStackProvider;
	}

	public IStatisticsDataProvider getCegarLoopStatisticsGenerator() {
		return mCegarLoopStatisticsGenerator;
	}

	public IElement getArtifact() {
		return mArtifact;
	}

	public List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> getFloydHoareAutomata() {
		return mFloydHoareAutomata;
	}

	// TODO: Move this to its own class (instead of result class)?
	// TODO: Use errorLocs instead of creating errNodesOfAllProc?
	public static <L extends IIcfgTransition<?>> CegarLoopResult<L> iterate(final IUltimateServiceProvider services,
			final DebugIdentifier name, final IIcfg<IcfgLocation> root, final TAPreferences taPrefs,
			final PredicateFactory predicateFactory, final Collection<IcfgLocation> errorLocs,
			final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation, final Concurrency automataType,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		final BasicCegarLoop<L> basicCegarLoop = constructCegarLoop(services, name, root, taPrefs,
				root.getCfgSmtToolkit(), predicateFactory, errorLocs, rawFloydHoareAutomataFromFile,
				computeHoareAnnotation, automataType, compositionFactory, transitionClazz);
		basicCegarLoop.setWitnessAutomaton(witnessAutomaton);

		final Result result = basicCegarLoop.iterate();
		basicCegarLoop.finish();

		final IProgramExecution<L, Term> programExecution;
		if (result == Result.UNSAFE || result == Result.UNKNOWN) {
			programExecution = basicCegarLoop.getRcfgProgramExecution();
		} else {
			programExecution = null;
		}

		final List<UnprovabilityReason> unprovabilityReasons;
		if (result == Result.UNKNOWN) {
			unprovabilityReasons = new ArrayList<>();
			unprovabilityReasons.add(basicCegarLoop.getReasonUnknown());
			unprovabilityReasons.addAll(UnprovabilityReason.getUnprovabilityReasons(programExecution));
		} else {
			unprovabilityReasons = null;
		}

		final IRunningTaskStackProvider runningTaskStackProvider;
		if (result == Result.TIMEOUT || result == Result.USER_LIMIT_ITERATIONS
				|| result == Result.USER_LIMIT_PATH_PROGRAM || result == Result.USER_LIMIT_TIME
				|| result == Result.USER_LIMIT_TRACEHISTOGRAM) {
			runningTaskStackProvider = basicCegarLoop.getRunningTaskStackProvider();
		} else {
			runningTaskStackProvider = null;
		}

		final IStatisticsDataProvider cegarLoopBenchmarkGenerator = basicCegarLoop.getCegarLoopBenchmark();

		final List<Pair<AbstractInterpolantAutomaton<L>, IPredicateUnifier>> floydHoareAutomata;
		if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
			floydHoareAutomata = new ArrayList<>(basicCegarLoop.getFloydHoareAutomata());
		} else {
			floydHoareAutomata = null;
		}

		if (computeHoareAnnotation && result == Result.SAFE) {
			basicCegarLoop.computeCFGHoareAnnotation();

			// final Set<? extends IcfgLocation> locsForHoareAnnotation =
			// TraceAbstractionUtils.getLocationsForWhichHoareAnnotationIsComputed(
			// root, taPrefs.getHoareAnnotationPositions());
			// computeHoareAnnotation(locsForHoareAnnotation);

			writeHoareAnnotationToLogger(services, root);
		}

		return new CegarLoopResult<>(result, programExecution, unprovabilityReasons, runningTaskStackProvider,
				cegarLoopBenchmarkGenerator, basicCegarLoop.getArtifact(), floydHoareAutomata);
	}

	private static <L extends IIcfgTransition<?>> BasicCegarLoop<L> constructCegarLoop(
			final IUltimateServiceProvider services, final DebugIdentifier name, final IIcfg<IcfgLocation> root,
			final TAPreferences taPrefs, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final Collection<IcfgLocation> errorLocs,
			final List<INestedWordAutomaton<String, String>> rawFloydHoareAutomataFromFile,
			final boolean computeHoareAnnotation, final Concurrency automataType,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		final LanguageOperation languageOperation = services.getPreferenceProvider(Activator.PLUGIN_ID)
				.getEnum(TraceAbstractionPreferenceInitializer.LABEL_LANGUAGE_OPERATION, LanguageOperation.class);

		BasicCegarLoop<L> result;
		if (languageOperation == LanguageOperation.DIFFERENCE) {
			if (taPrefs.interpolantAutomaton() == InterpolantAutomaton.TOTALINTERPOLATION) {
				result = new CegarLoopSWBnonRecursive<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
						taPrefs.interpolation(), taPrefs.computeHoareAnnotation(), services, compositionFactory,
						transitionClazz);
			} else {
				switch (automataType) {
				case FINITE_AUTOMATA: {
					switch (taPrefs.getFloydHoareAutomataReuse()) {
					case EAGER:
						result = new EagerReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
								taPrefs.interpolation(), computeHoareAnnotation, services, Collections.emptyList(),
								rawFloydHoareAutomataFromFile, compositionFactory, transitionClazz);
						break;
					case LAZY_IN_ORDER:
						result = new LazyReuseCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
								taPrefs.interpolation(), computeHoareAnnotation, services, Collections.emptyList(),
								rawFloydHoareAutomataFromFile, compositionFactory, transitionClazz);
						break;
					case NONE:
						result = new BasicCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
								taPrefs.interpolation(), computeHoareAnnotation, services, compositionFactory,
								transitionClazz);
						break;
					default:
						throw new AssertionError("unknown value: " + taPrefs.getFloydHoareAutomataReuse());
					}
				}
					break;
				case PETRI_NET: {
					if (taPrefs.getFloydHoareAutomataReuse() != FloydHoareAutomataReuse.NONE) {
						throw new UnsupportedOperationException("Reuse with Petri net-based analysis");
					}
					result = new CegarLoopForPetriNet<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
							services, compositionFactory, transitionClazz);
				}
					break;
				default:
					throw new AssertionError("unknown value: " + automataType);
				}
			}
		} else {
			result = new IncrementalInclusionCegarLoop<>(name, root, csToolkit, predicateFactory, taPrefs, errorLocs,
					taPrefs.interpolation(), computeHoareAnnotation, services, languageOperation, compositionFactory,
					transitionClazz);
		}
		return result;
	}

	private static void writeHoareAnnotationToLogger(final IUltimateServiceProvider services,
			final IIcfg<IcfgLocation> root) {
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		for (final Entry<String, Map<DebugIdentifier, IcfgLocation>> proc2label2pp : root.getProgramPoints()
				.entrySet()) {
			for (final IcfgLocation pp : proc2label2pp.getValue().values()) {
				final HoareAnnotation hoare = HoareAnnotation.getAnnotation(pp);
				if (hoare != null && !hoare.getFormula().toString().equals("true")) {
					logger.info("At program point  " + prettyPrintProgramPoint(pp) + "  the Hoare annotation is:  "
							+ hoare.getFormula());
				} else if (EXTENDED_HOARE_ANNOTATION_LOGGING) {
					if (hoare == null) {
						logger.info("For program point  " + prettyPrintProgramPoint(pp)
								+ "  no Hoare annotation was computed.");
					} else {
						logger.info("At program point  " + prettyPrintProgramPoint(pp) + "  the Hoare annotation is:  "
								+ hoare.getFormula());
					}
				}
			}
		}
	}

	private static String prettyPrintProgramPoint(final IcfgLocation pp) {
		final ILocation loc = ILocation.getAnnotation(pp);
		if (loc == null) {
			return "";
		}
		final int startLine = loc.getStartLine();
		final int endLine = loc.getEndLine();
		final StringBuilder sb = new StringBuilder();
		sb.append(pp);
		if (startLine == endLine) {
			sb.append("(line " + startLine + ")");
		} else {
			sb.append("(lines " + startLine + " " + endLine + ")");
		}
		return sb.toString();
	}

}
