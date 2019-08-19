/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.MergedLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult.CategorizedProgramPoint;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult.CheckPoint;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult.LoopFreeSegment;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult.LoopFreeSegmentWithStatePair;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult.LoopHead;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult.ProcedureEntry;
import de.uni_freiburg.informatik.ultimate.core.lib.results.AnnotationCheckResult.ProcedureExit;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.BasicInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Check given annotation without inferring invariants.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class InvariantChecker {
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<IcfgLocation> mIcfg;

	private final LoopLocations mLoopLocations;
	private IResultWithSeverity mResultForUltimateUser;

	public enum ProgramPointType {
		ENTRY, LOOP_HEAD, ERROR_LOC, UNKNOWN, LOOP_INVARIANT_ERROR_LOC;
	}

	public InvariantChecker(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mIcfg = icfg;
		mLoopLocations = extractLoopLocations(mIcfg);
		if (!mLoopLocations.getLoopLocWithoutInvariant().isEmpty()) {

			final String shortDescription = "Not every loop was annotated with an invariant.";
			final String longDescription = "Missing invariants at: "
					+ icfgLocationsToListOfLineNumbers(mLoopLocations.getLoopLocWithoutInvariant());
			final Severity severity = Severity.ERROR;
			mResultForUltimateUser = new GenericResultAtElement<>(
					mLoopLocations.getLoopLocWithoutInvariant().get(0).getOutgoingEdges().get(0), Activator.PLUGIN_ID,
					mServices.getBacktranslationService(), shortDescription, longDescription, severity);
			return;
		}
		mLogger.info("Found " + mIcfg.getLoopLocations().size() + " loops.");

		final Set<IcfgLocation> loopLocsAndNonLoopErrorLocs = new HashSet<>();
		final Map<String, Set<IcfgLocation>> proc2errNodes = icfg.getProcedureErrorNodes();
		for (final Entry<String, Set<IcfgLocation>> entry : proc2errNodes.entrySet()) {
			for (final IcfgLocation errorLoc : entry.getValue()) {
				final IcfgEdge loopErrorEdge = mLoopLocations.getLoopErrorLoc2errorEdge().get(errorLoc);
				if (loopErrorEdge != null) {
					loopLocsAndNonLoopErrorLocs.add(loopErrorEdge.getSource());
				} else {
					loopLocsAndNonLoopErrorLocs.add(errorLoc);
				}
			}
		}

		final List<TwoPointSubgraphDefinition> tpsds =
				findTwoPointSubgraphDefinitions(icfg, mLoopLocations, loopLocsAndNonLoopErrorLocs);
		final String message = message24(tpsds);
		mLogger.info("Will check " + message);
		final Set<TwoPointSubgraphDefinition> validTpsds = new HashSet<>();
		final Set<TwoPointSubgraphDefinition> unknownTpsds = new HashSet<>();
		final Map<TwoPointSubgraphDefinition, EdgeCheckResult> invalidTpsds = new HashMap<>();
		for (final TwoPointSubgraphDefinition tpsd : tpsds) {
			final IcfgLocation startLoc = tpsd.getStartLocation();
			final IcfgLocation errorLoc = tpsd.getEndLocation();
			IcfgEdge omitEdge = mLoopLocations.getLoopLoc2errorEdge().get(startLoc);
			if (!tpsd.getSubgraphEdges().contains(omitEdge)) {
				omitEdge = null;
			}
			final AcyclicSubgraphMerger asm = new AcyclicSubgraphMerger(mServices, mIcfg, tpsd.getSubgraphEdges(),
					tpsd.getStartLocation(), omitEdge, Collections.singleton(tpsd.getEndLocation()));
			final UnmodifiableTransFormula tf = asm.getTransFormula(errorLoc);
			Objects.requireNonNull(tf);
			final EdgeCheckResult ecr = doCheck(startLoc, tf, errorLoc);
			switch (ecr.getValidity()) {
			case INVALID:
				invalidTpsds.put(tpsd, ecr);
				break;
			case NOT_CHECKED:
				throw new AssertionError("failed to perfrom check");
			case UNKNOWN:
				unknownTpsds.add(tpsd);
				break;
			case VALID:
				validTpsds.add(tpsd);
				break;
			default:
				throw new AssertionError("illegal result: " + ecr.getValidity());
			}
		}
		final List<LoopFreeSegment<IcfgEdge>> validSegments = twoPointSubgraphsToSegments(validTpsds);
		final List<LoopFreeSegment<IcfgEdge>> unknownSegments = twoPointSubgraphsToSegments(unknownTpsds);
		final List<LoopFreeSegmentWithStatePair<IcfgEdge, Term>> invalidSegments = twoPointSubgraphsToSegments(
				invalidTpsds);
		mResultForUltimateUser = new AnnotationCheckResult<IcfgEdge, Term>(Activator.PLUGIN_ID,
				mServices.getBacktranslationService(), validSegments, unknownSegments, invalidSegments);
	}

	private String icfgLocationsToListOfLineNumbers(final List<IcfgLocation> loopLocWithoutInvariant) {
		final TreeSet<Integer> lineNumbersSorted = loopLocWithoutInvariant.stream()
				.map(x -> guessLocation(x).getStartLine()).collect(Collectors.toCollection(TreeSet::new));
		final String result = lineNumbersSorted.stream().map(x -> "line " + x.toString())
				.collect(Collectors.joining(", "));
		return result;
	}

	private List<LoopFreeSegmentWithStatePair<IcfgEdge, Term>>
			twoPointSubgraphsToSegments(final Map<TwoPointSubgraphDefinition, EdgeCheckResult> mInvalid) {
		final List<LoopFreeSegmentWithStatePair<IcfgEdge, Term>> result = new ArrayList<>();
		for (final Entry<TwoPointSubgraphDefinition, EdgeCheckResult> entry : mInvalid.entrySet()) {
			result.add(twoPointSubgraphToSegment(entry.getKey(), entry.getValue()));
		}
		return result;
	}

	private LoopFreeSegmentWithStatePair<IcfgEdge, Term>
			twoPointSubgraphToSegment(final TwoPointSubgraphDefinition tpsd, final EdgeCheckResult value) {
		final CategorizedProgramPoint cppBefore = constructCategorizedProgramPoint(tpsd.getStartLocation());
		final CategorizedProgramPoint cppAfter= constructCategorizedProgramPoint(tpsd.getEndLocation());
		final LoopFreeSegmentWithStatePair<IcfgEdge, Term> result = new LoopFreeSegmentWithStatePair<>(cppBefore,
				cppAfter, value.getCtxPre(), value.getCtxPost());
		return result;
	}

	private CategorizedProgramPoint constructCategorizedProgramPoint(final IcfgLocation programPoint) {
		final ILocation location = guessLocation(programPoint);
		final ProgramPointType programPointType = classify(programPoint);
		final CategorizedProgramPoint result;
		switch (programPointType) {
		case ENTRY:
			result = new ProcedureEntry(location, programPoint.getProcedure());
			break;
		case ERROR_LOC:
			final Check check = Check.getAnnotation(programPoint);
			if (check == null) {
				throw new AssertionError(
						"program point " + programPoint + " is error location but does not have a Check");
			}
			if (check.getSpec().equals(Collections.singleton(Check.Spec.POST_CONDITION))) {
				result = new ProcedureExit(location, programPoint.getProcedure());
			} else {
				result = new CheckPoint(location, Check.getAnnotation(programPoint));
			}
			break;
		case LOOP_HEAD:
			result = new LoopHead(location);
			break;
		case LOOP_INVARIANT_ERROR_LOC:
			result = new LoopHead(location);
			break;
		case UNKNOWN:
		default:
			throw new AssertionError("unable to categorize program point " + programPoint);
		}
		return result;
	}

	private List<LoopFreeSegment<IcfgEdge>> twoPointSubgraphsToSegments(final Set<TwoPointSubgraphDefinition> mValid) {
		final List<LoopFreeSegment<IcfgEdge>> result = new ArrayList<>();
		for (final TwoPointSubgraphDefinition tpsd : mValid) {
			result.add(twoPointSubgraphToSegment(tpsd));
		}
		return result;
	}

	private LoopFreeSegment<IcfgEdge> twoPointSubgraphToSegment(final TwoPointSubgraphDefinition tpsd) {
		final CategorizedProgramPoint cppBefore = constructCategorizedProgramPoint(tpsd.getStartLocation());
		final CategorizedProgramPoint cppAfter= constructCategorizedProgramPoint(tpsd.getEndLocation());
		final LoopFreeSegment<IcfgEdge> result = new LoopFreeSegment<>(cppBefore, cppAfter);
		return result;
	}

	private ILocation guessLocation(final IcfgLocation programPoint) {
		final ProgramPointType programPointType = classify(programPoint);
		final IcfgEdge someEdge;
		switch (programPointType) {
		case ENTRY:
		case LOOP_HEAD:
			someEdge = programPoint.getOutgoingEdges().get(0);
			break;
		case ERROR_LOC:
		case LOOP_INVARIANT_ERROR_LOC:
			someEdge = programPoint.getIncomingEdges().get(0);
			break;
		case UNKNOWN:
		default:
			throw new AssertionError("unable to determine type of program point");
		}
		final ILocation loc = ILocation.getAnnotation(someEdge);
		final ILocation result;
		if (loc instanceof MergedLocation) {
			result = ((MergedLocation) loc).getOriginLocations().get(0);
		} else {
			result = loc;
		}
		return result;
	}

	private String message24(final List<TwoPointSubgraphDefinition> tpsds) {
		final HashRelation<Pair<ProgramPointType, ProgramPointType>, TwoPointSubgraphDefinition> hr = new HashRelation<>();
		for (final TwoPointSubgraphDefinition tpsd : tpsds) {
			final ProgramPointType startType = classify(tpsd.getStartLocation());
			final ProgramPointType endType = classify(tpsd.getEndLocation());
			hr.addPair(new Pair(startType, endType), tpsd);
		}
		boolean isFirst = true;
		final StringBuilder sb = new StringBuilder();
		for (final Pair<ProgramPointType, ProgramPointType> dom : hr.getDomain()) {
			final int number = hr.numberOfPairsWithGivenDomainElement(dom);
			if (!isFirst) {
				sb.append(", ");
			}
			sb.append(number + " loop-free subgraphs from " + getNiceSubgraphPointDescription(dom.getFirst()) + " to "
					+ getNiceSubgraphPointDescription(dom.getSecond()));
			isFirst = false;
		}
		return sb.toString();
	}

	private List<TwoPointSubgraphDefinition> findTwoPointSubgraphDefinitions(final IIcfg<IcfgLocation> icfg,
			final LoopLocations loopLocations, final Set<IcfgLocation> loopLocsAndNonLoopErrorLocs) {
		final List<TwoPointSubgraphDefinition> tpsds = new ArrayList<>();
		for (final IcfgLocation backwardStartLoc : loopLocsAndNonLoopErrorLocs) {
			tpsds.addAll(findSubgraphGivenEndLocation(backwardStartLoc, loopLocations, icfg));
		}
		return tpsds;
	}

	private static LoopLocations extractLoopLocations(final IIcfg<IcfgLocation> icfg) {
		final Map<IcfgLocation, IcfgEdge> loopLoc2errorEdge = new HashMap<>();
		final Map<IcfgLocation, IcfgEdge> loopErrorLoc2errorEdge = new HashMap<>();
		final List<IcfgLocation> loopLocWithoutInvariant = new ArrayList<>();
		for (final IcfgLocation loopLoc : icfg.getLoopLocations()) {
			final IcfgEdge errorEdge = getErrorEdgeForLoopInvariant(loopLoc);
			if (errorEdge == null) {
				loopLocWithoutInvariant.add(loopLoc);
			} else {
				loopLoc2errorEdge.put(loopLoc, errorEdge);
				loopErrorLoc2errorEdge.put(errorEdge.getTarget(), errorEdge);
			}
		}
		return new LoopLocations(loopLoc2errorEdge, loopErrorLoc2errorEdge, loopLocWithoutInvariant);
	}

	/**
	 * Find all loop-free subgraphs that start in a loop location or a procedure entry and end at the location endLoc
	 *
	 * @param backwardStartLoc
	 *            Cutpoint where we start for predecessor cutpoints For a loop location, this is the loop head and not
	 *            the corresponding error location.
	 */
	private List<TwoPointSubgraphDefinition> findSubgraphGivenEndLocation(final IcfgLocation backwardStartLoc,
			final LoopLocations loopLocations, final IIcfg<IcfgLocation> icfg) {
		final List<TwoPointSubgraphDefinition> tpsds = new ArrayList<>();
		final ArrayDeque<IcfgEdge> worklistBackward = new ArrayDeque<>();
		final Set<IcfgEdge> seenBackward = new HashSet<>();
		final Set<IcfgLocation> startLocs = new HashSet<>();
		worklistBackward.addAll(backwardStartLoc.getIncomingEdges());
		seenBackward.addAll(backwardStartLoc.getIncomingEdges());
		while (!worklistBackward.isEmpty()) {
			final IcfgEdge edge = worklistBackward.removeFirst();
			final IcfgLocation loc = edge.getSource();
			if (icfg.getInitialNodes().contains(loc) || icfg.getLoopLocations().contains(loc)) {
				startLocs.add(loc);
			} else {
				for (final IcfgEdge pred : loc.getIncomingEdges()) {
					if (!seenBackward.contains(pred)) {
						seenBackward.add(pred);
						worklistBackward.add(pred);
					}
				}
			}
		}
		for (final IcfgLocation startLoc : startLocs) {
			final TwoPointSubgraphDefinition tpsd = extractSubgraphGivenStartAndEnd(startLoc, backwardStartLoc,
					Collections.unmodifiableSet(seenBackward), loopLocations, icfg);
			if (loopLocations.getLoopLoc2errorEdge().containsKey(backwardStartLoc)) {
				final IcfgEdge errorEdge = loopLocations.getLoopLoc2errorEdge().get(backwardStartLoc);
				final IcfgLocation errorLoc = errorEdge.getTarget();
				if (tpsd.getEndLocation() != errorLoc) {
					throw new AssertionError("wrong error loc");
				}
			} else {
				if (tpsd.getEndLocation() != backwardStartLoc) {
					throw new AssertionError("wrong error loc");
				}
			}
			mLogger.info(message23(tpsd));
			tpsds.add(tpsd);
		}
		return tpsds;
	}

	/**
	 * Collect all edges in the subgraph that starts in startLoc and ends in backwardStartLoc In case backwardStartLoc
	 * is a loop head, the corresponding error location becomes the end location of the resulting
	 * TwoPointSubgraphDefinition.
	 */
	private static TwoPointSubgraphDefinition extractSubgraphGivenStartAndEnd(final IcfgLocation startLoc,
			final IcfgLocation backwardStartLoc, final Set<IcfgEdge> seenBackward, final LoopLocations loopLocations,
			final IIcfg<IcfgLocation> icfg) {
		final ArrayDeque<IcfgEdge> worklistForward = new ArrayDeque<>();
		final Set<IcfgEdge> seenForward = new HashSet<>();
		final Set<IcfgLocation> errorLocations = new HashSet<>();
		for (final IcfgEdge edge : startLoc.getOutgoingEdges()) {
			if (seenBackward.contains(edge)) {
				worklistForward.add(edge);
				seenForward.add(edge);
			}
		}
		while (!worklistForward.isEmpty()) {
			final IcfgEdge currentEdge = worklistForward.removeFirst();
			final IcfgLocation loc = currentEdge.getTarget();
			if (loc == backwardStartLoc) {
				if (icfg.getLoopLocations().contains(loc)) {
					final IcfgEdge loopErrorEdge = loopLocations.getLoopLoc2errorEdge().get(loc);
					seenForward.add(loopErrorEdge);
					errorLocations.add(loopErrorEdge.getTarget());
				} else if (icfg.getProcedureErrorNodes().get(loc.getProcedure()).contains(loc)) {
					errorLocations.add(loc);
				} else {
					throw new AssertionError("unknown backwardStartLoc");
				}
			} else {
				for (final IcfgEdge succEdge : loc.getOutgoingEdges()) {
					if (!seenBackward.contains(succEdge)) {
						// does not belong to search space
						continue;
					}
					seenForward.add(succEdge);
					worklistForward.add(succEdge);
				}
			}
		}
		assert errorLocations.size() == 1;
		final IcfgLocation errorLoc = errorLocations.iterator().next();
		return new TwoPointSubgraphDefinition(startLoc, seenForward, errorLoc);
	}

	private String message23(final TwoPointSubgraphDefinition tpsd) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Will check inductivity from ");
		sb.append(classify(tpsd.getStartLocation()));
		sb.append(" ");
		sb.append(tpsd.getStartLocation());
		sb.append(" to ");
		sb.append(classify(tpsd.getEndLocation()));
		sb.append(" ");
		sb.append(tpsd.getEndLocation());
		sb.append(". ");
		sb.append("Corresponding subgraph has " + tpsd.getSubgraphEdges().size() + " edges.");
		return sb.toString();
	}

	ProgramPointType classify(final IcfgLocation loc) {
		if (mIcfg.getLoopLocations().contains(loc)) {
			return ProgramPointType.LOOP_HEAD;
		} else if (mLoopLocations.getLoopErrorLoc2errorEdge().containsKey(loc)) {
			return ProgramPointType.LOOP_INVARIANT_ERROR_LOC;
		} else {
			final String proc = loc.getProcedure();
			if (mIcfg.getProcedureEntryNodes().get(proc).equals(loc)) {
				return ProgramPointType.ENTRY;
			} else if (mIcfg.getProcedureErrorNodes().get(proc).contains(loc)) {
				return ProgramPointType.ERROR_LOC;
			} else {
				return ProgramPointType.UNKNOWN;
			}
		}
	}

	private EdgeCheckResult doCheck(final IcfgLocation startLoc, final UnmodifiableTransFormula tf,
			final IcfgLocation errorLoc) {
		final IncrementalHoareTripleChecker htc = new IncrementalHoareTripleChecker(mIcfg.getCfgSmtToolkit(), true);
		final PredicateFactory pf = new PredicateFactory(mServices, mIcfg.getCfgSmtToolkit().getManagedScript(),
				mIcfg.getCfgSmtToolkit().getSymbolTable());
		final IPredicate truePredicate =
				pf.newPredicate(mIcfg.getCfgSmtToolkit().getManagedScript().getScript().term("true"));
		final IPredicate falsePredicate =
				pf.newPredicate(mIcfg.getCfgSmtToolkit().getManagedScript().getScript().term("false"));
		final Validity validity = htc.checkInternal(truePredicate,
				new BasicInternalAction(startLoc.getProcedure(), errorLoc.getProcedure(), tf), falsePredicate);
		final EdgeCheckResult ecr;
		switch (validity) {
		case INVALID:
			final ProgramState<Term> ctxPre = htc.getCounterexampleStatePrecond();
			final ProgramState<Term> ctxPost = htc.getCounterexampleStatePostcond();
			ecr = new EdgeCheckResult(validity, ctxPre, ctxPost);
			break;
		case NOT_CHECKED:
			throw new AssertionError();
		case UNKNOWN:
			ecr = new EdgeCheckResult(validity, null, null);
			mLogger.info("unknown inductivity: todo good error message");
			break;
		case VALID:
			ecr = new EdgeCheckResult(validity, null, null);
			mLogger.info(generateMessage(startLoc, errorLoc, true));
			break;
		default:
			throw new AssertionError();
		}
		htc.releaseLock();
		return ecr;
	}

	private String generateMessage(final IcfgLocation startLoc, final IcfgLocation errorLoc, final boolean positive) {
		final StringBuilder sb = new StringBuilder();
		sb.append("The annotation(s) from ");
		sb.append(getType(startLoc));
		sb.append(" at line ");
		// sb.append(startLoc.getStartLine());
		sb.append(" to ");
		sb.append(getType(startLoc));
		sb.append(" at line ");
		// sb.append(startLoc.getStartLine());
		sb.append(" is");
		if (!positive) {
			sb.append(" NOT");
		}
		sb.append(" inductive.");
		return sb.toString();
	}

	private static String getType(final IcfgLocation startLoc) {
		if (isInvariant(startLoc)) {
			return "loop head";
		} else if (isErrorLoc(startLoc)) {
			return "error location";
		} else if (isLoopLoc(startLoc)) {
			return "loop head";
		} else {
			return "entry";
		}
	}

	public static <E extends IIcfgTransition<IcfgLocation>> Set<E> collectAdjacentEdges(final IIcfg<IcfgLocation> icfg,
			final Set<IcfgLocation> locations) {
		final Set<E> result = new HashSet<>();
		for (final IcfgLocation loc : locations) {
			loc.getOutgoingEdges();
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				if (locations.contains(edge.getTarget())) {
					result.add((E) edge);
				}
			}
		}
		return result;
	}

	private static void processForward(final ArrayDeque<IcfgLocation> worklistForward, final Set<IcfgLocation> seenForward,
			final Set<IcfgLocation> errorLocations, final IcfgLocation succLoc, final boolean checkForErrorLocs) {
		seenForward.add(succLoc);
		final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(succLoc);
		if (loa != null) {
			final IcfgLocation eLoc = getErrorEdgeForLoopInvariant(succLoc).getTarget();
			seenForward.add(eLoc);
			errorLocations.add(eLoc);
		} else {
			final Check check = Check.getAnnotation(succLoc);
			if (checkForErrorLocs && check != null) {
				seenForward.add(succLoc);
				errorLocations.add(succLoc);
			} else {
				seenForward.add(succLoc);
				worklistForward.add(succLoc);
			}
		}
	}

	private static IcfgEdge getErrorEdgeForLoopInvariant(final IcfgLocation loopLoc) {
		IcfgEdge result = null;
		for (final IcfgEdge succEdge : loopLoc.getOutgoingEdges()) {
			final IcfgLocation succLoc = succEdge.getTarget();
			if (isInvariant(succLoc)) {
				if (result == null) {
					result = succEdge;
				} else {
					throw new UnsupportedOperationException("several invariants");
				}
			}
		}
		return result;
	}

	private static boolean isInvariant(final IcfgLocation loc) {
		final Check check = Check.getAnnotation(loc);
		if (check != null) {
			final EnumSet<Spec> specs = check.getSpec();
			// if (specs.size() == 1) {
			return specs.contains(Spec.INVARIANT);
			// } else {
			// throw new UnsupportedOperationException("several specs");
			// }
		}
		return false;
	}

	private static boolean isErrorLoc(final IcfgLocation loc) {
		final Check check = Check.getAnnotation(loc);
		return (check != null);
	}

	private static boolean isLoopLoc(final IcfgLocation loc) {
		final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(loc);
		return (loa != null);
	}

	private String getNiceSubgraphPointDescription(final ProgramPointType lt) {
		switch (lt) {
		case ENTRY:
			return "procedure entry";
		case ERROR_LOC:
			return "error location";
		case LOOP_HEAD:
			return "loop head";
		case LOOP_INVARIANT_ERROR_LOC:
			return "loop head";
		case UNKNOWN:
			return "unspecified location type";
		default:
			throw new AssertionError("unknown location type " + lt);
		}
	}

	public IResultWithSeverity getResultForUltimateUser() {
		return mResultForUltimateUser;
	}

	private static class TwoPointSubgraphDefinition {
		private final IcfgLocation mStartLocation;
		private final Set<IcfgEdge> mSubgraphEdges;
		private final IcfgLocation mEndLocation;

		public TwoPointSubgraphDefinition(final IcfgLocation startLocation, final Set<IcfgEdge> subgraphEdges,
				final IcfgLocation endLocation) {
			super();
			mStartLocation = startLocation;
			mSubgraphEdges = subgraphEdges;
			mEndLocation = endLocation;
		}

		public IcfgLocation getStartLocation() {
			return mStartLocation;
		}

		public Set<IcfgEdge> getSubgraphEdges() {
			return mSubgraphEdges;
		}

		public IcfgLocation getEndLocation() {
			return mEndLocation;
		}
	}

	private static class EdgeCheckResult {

		private final Validity mValidity;
		private final ProgramState<Term> mCtxPre;
		private final ProgramState<Term> mCtxPost;

		public EdgeCheckResult(final Validity validity, final ProgramState<Term> ctxPre,
				final ProgramState<Term> ctxPost) {
			mValidity = validity;
			mCtxPre = ctxPre;
			mCtxPost = ctxPost;
		}

		public Validity getValidity() {
			return mValidity;
		}

		public ProgramState<Term> getCtxPre() {
			return mCtxPre;
		}

		public ProgramState<Term> getCtxPost() {
			return mCtxPost;
		}

	}

	private static class LoopLocations {
		public final Map<IcfgLocation, IcfgEdge> mLoopLoc2errorEdge;
		public final Map<IcfgLocation, IcfgEdge> mLoopErrorLoc2errorEdge;
		public final List<IcfgLocation> mLoopLocWithoutInvariant;

		public LoopLocations(final Map<IcfgLocation, IcfgEdge> loopLoc2errorEdge,
				final Map<IcfgLocation, IcfgEdge> loopErrorLoc2errorEdge,
				final List<IcfgLocation> loopLocWithoutInvariant) {
			mLoopLoc2errorEdge = loopLoc2errorEdge;
			mLoopErrorLoc2errorEdge = loopErrorLoc2errorEdge;
			mLoopLocWithoutInvariant = loopLocWithoutInvariant;
		}

		public Map<IcfgLocation, IcfgEdge> getLoopLoc2errorEdge() {
			return mLoopLoc2errorEdge;
		}

		public Map<IcfgLocation, IcfgEdge> getLoopErrorLoc2errorEdge() {
			return mLoopErrorLoc2errorEdge;
		}

		public List<IcfgLocation> getLoopLocWithoutInvariant() {
			return mLoopLocWithoutInvariant;
		}

	}

}
