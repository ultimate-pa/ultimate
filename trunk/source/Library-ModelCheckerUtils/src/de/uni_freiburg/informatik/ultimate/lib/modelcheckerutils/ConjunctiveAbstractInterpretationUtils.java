/*
 * Copyright (C) 2024 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.IncrementalImplicationChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * This class provides an implementation of abstract interpretation whose focus
 * is not speed and precision but simplicity. The fixpoint iteration will never
 * split nodes hence invariants are typically conjunctions. <br />
 * Warning: The interface of this class will change.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */

public class ConjunctiveAbstractInterpretationUtils {

	public static enum Widening {
		INTERSECTION, SMT_SOLVER, POLY_PAC,
	}

	private ConjunctiveAbstractInterpretationUtils() {
		// do not instantiate
	}

	public static <LOC extends IcfgLocation> Map<IcfgLocation, IPredicate> computeInvariants(
			final IUltimateServiceProvider services, final IIcfg<LOC> icfg, final Widening widening) {
		final BasicPredicateFactory predFac = new BasicPredicateFactory(services,
				icfg.getCfgSmtToolkit().getManagedScript(), icfg.getCfgSmtToolkit().getSymbolTable());
		final Map<IcfgLocation, IPredicate> result = new HashMap<>();
		final ArrayDeque<LOC> worklist = new ArrayDeque<>();
		initializeMapAndWorklist(icfg, worklist, predFac, result);
		doFixpointIteration(services, icfg, predFac, widening, worklist, result);
		final ILogger logger = services.getLoggingService().getLogger(ConjunctiveAbstractInterpretationUtils.class);
		if (logger.isInfoEnabled()) {
			logInvariantInformation(logger, icfg, result);
		}
		return result;
	}

	private static <LOC extends IcfgLocation> void logInvariantInformation(final ILogger logger, final IIcfg<LOC> icfg,
			final Map<IcfgLocation, IPredicate> result) {
		int trueInvariants = 0;
		int falseInvariants = 0;
		int errorLocations = 0;
		int errorLocationsLabelledByFalse = 0;
		for (final Entry<IcfgLocation, IPredicate> entry : result.entrySet()) {

			if (IcfgUtils.isErrorLocation(icfg, entry.getKey())) {
				errorLocations++;
				if (SmtUtils.isFalseLiteral(entry.getValue().getFormula())) {
					errorLocationsLabelledByFalse++;
				}
			}

			if (SmtUtils.isTrueLiteral(entry.getValue().getFormula())) {
				trueInvariants++;
			} else if (SmtUtils.isFalseLiteral(entry.getValue().getFormula())) {
				falseInvariants++;
			}
		}
		logger.info(String.format(
				"Applied ConjunctiveAbstractInterpretation to ICFG %s: %s locations (thereof %s times true, %s times false). ICFG has %s error locations (thereof %s labelled by false).",
				icfg.getIdentifier(), result.size(), trueInvariants, falseInvariants, errorLocations,
				errorLocationsLabelledByFalse));
	}

	private static <LOC extends IcfgLocation> void initializeMapAndWorklist(final IIcfg<LOC> icfg,
			final ArrayDeque<LOC> worklist, final BasicPredicateFactory predFac,
			final Map<IcfgLocation, IPredicate> result) {
		final IPredicate truePredicate = constructTruePredicate(icfg, predFac);
		final IPredicate falsePredicate = constructFalsePredicate(icfg, predFac);
		for (final Entry<String, Map<DebugIdentifier, LOC>> procToPps : icfg.getProgramPoints().entrySet()) {
			for (final Entry<DebugIdentifier, LOC> entry : procToPps.getValue().entrySet()) {
				final LOC pp = entry.getValue();
				if (icfg.getInitialNodes().contains(pp)) {
					// initialize initial nodes with empty set (which represents true)
					result.put(pp, truePredicate);
					worklist.add(pp);
				} else {
					// initialize all other nodes with false
					result.put(pp, falsePredicate);
				}
			}
		}
	}

	private static <LOC extends IcfgLocation> IPredicate constructFalsePredicate(final IIcfg<LOC> icfg,
			final BasicPredicateFactory predFac) {
		return predFac.newPredicate(icfg.getCfgSmtToolkit().getManagedScript().getScript().term("false"));
	}

	private static <LOC extends IcfgLocation> IPredicate constructTruePredicate(final IIcfg<LOC> icfg,
			final BasicPredicateFactory predFac) {
		return predFac.newPredicate(icfg.getCfgSmtToolkit().getManagedScript().getScript().term("true"));
	}

	private static <LOC extends IcfgLocation> void doFixpointIteration(final IUltimateServiceProvider services,
			final IIcfg<LOC> icfg, final BasicPredicateFactory predFac, final Widening widening,
			final ArrayDeque<LOC> worklist, final Map<IcfgLocation, IPredicate> result) {
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		final PredicateTransformer<Term, IPredicate, TransFormula> pt = new PredicateTransformer<>(mgdScript,
				new TermDomainOperationProvider(services, mgdScript));
		long iterations = 0;
		while (!worklist.isEmpty()) {
			final LOC src = worklist.removeFirst();
			final IPredicate srcPred = result.get(src);
			for (final IcfgEdge edge : src.getOutgoingEdges()) {
				final Term postcondition;
				if (edge instanceof IIcfgInternalTransition) {
					postcondition = pt.strongestPostcondition(srcPred, edge.getTransformula());
				} else if (edge instanceof IIcfgSummaryTransition) {
					if (((IIcfgSummaryTransition) edge).calledProcedureHasImplementation()) {
						// do nothing, ignore this edge
						continue;
					} else {
						// handle like an internal edge
						postcondition = pt.strongestPostcondition(srcPred, edge.getTransformula());
					}
				} else if (edge instanceof IIcfgCallTransition) {
					final String callee = edge.getSucceedingProcedure();
					final TransFormula localVarAssignment = edge.getTransformula();
					final TransFormula globalVarAssignments = icfg.getCfgSmtToolkit().getOldVarsAssignmentCache()
							.getGlobalVarsAssignment(callee);
					final TransFormula oldVarAssignments = icfg.getCfgSmtToolkit().getOldVarsAssignmentCache()
							.getGlobalVarsAssignment(callee);
					final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure = icfg.getCfgSmtToolkit()
							.getModifiableGlobalsTable().getModifiedBoogieVars(callee);
					postcondition = pt.strongestPostconditionCall(srcPred, localVarAssignment, globalVarAssignments,
							oldVarAssignments, modifiableGlobalsOfCalledProcedure);
				} else if (edge instanceof IIcfgReturnTransition) {
					final String callee = edge.getPrecedingProcedure();
					final IIcfgCallTransition call = ((IIcfgReturnTransition) edge).getCorrespondingCall();
					final TransFormula oldVarAssignments = icfg.getCfgSmtToolkit().getOldVarsAssignmentCache()
							.getGlobalVarsAssignment(callee);
					final Set<IProgramNonOldVar> modifiableGlobalsOfCalledProcedure = icfg.getCfgSmtToolkit()
							.getModifiableGlobalsTable().getModifiedBoogieVars(callee);
					final IPredicate callerPred = result.get(((IIcfgReturnTransition) edge).getCallerProgramPoint());
					postcondition = pt.strongestPostconditionReturn(srcPred, callerPred, edge.getTransformula(),
							call.getLocalVarsAssignment(), oldVarAssignments, modifiableGlobalsOfCalledProcedure);
				} else {
					throw new AssertionError("Yet unsupported: " + edge.getClass().getSimpleName());
				}
				final LOC target = (LOC) edge.getTarget();
				final IPredicate oldTargetPredicate = result.get(target);
				final IPredicate newTargetPredicate = widen(services, icfg, predFac, widening, oldTargetPredicate,
						postcondition);
				if (newTargetPredicate != null) {
					result.put(target, newTargetPredicate);
					worklist.add(target);
				}
			}
			iterations++;
		}
		System.out.println("Iterations " + iterations);
	}

	private static <LOC extends IcfgLocation> IPredicate widen(final IUltimateServiceProvider services,
			final IIcfg<LOC> icfg, final BasicPredicateFactory predFac, final Widening widen,
			final IPredicate oldTargetPredicate, final Term postcondition) {
		final Set<Term> oldConjuncts = new HashSet<>(
				Arrays.asList(SmtUtils.getConjuncts(oldTargetPredicate.getFormula())));
		final Set<Term> postconditionConjuncts = new HashSet<>(Arrays.asList(SmtUtils.getConjuncts(postcondition)));
		final Term newConjunction;
		if (isFalse(oldConjuncts)) {
			newConjunction = postcondition;
		} else {
			final Set<Term> newConjuncts;
			switch (widen) {
			case INTERSECTION:
				newConjuncts = widenNaively(oldConjuncts, postconditionConjuncts);
				break;
			case POLY_PAC:
				throw new AssertionError("Not yet implemented.");
			case SMT_SOLVER:
				newConjuncts = widenBySolver(services, icfg.getCfgSmtToolkit().getManagedScript(), predFac,
						oldTargetPredicate, postcondition, oldConjuncts, postconditionConjuncts);
				break;
			default:
				throw new AssertionError("Unknown value");
			}
			newConjunction = SmtUtils.and(icfg.getCfgSmtToolkit().getManagedScript().getScript(), newConjuncts);
		}
		if (newConjunction.equals(oldTargetPredicate.getFormula())) {
			return null;
		} else {
			return predFac.newPredicate(newConjunction);
		}
	}

	public static Set<Term> widenNaively(final Set<Term> oldConjuncts, final Set<Term> postconditionConjuncts) {
		return DataStructureUtils.intersection(postconditionConjuncts, oldConjuncts);
	}

	public static Set<Term> widenBySolver(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predFac, final IPredicate oldPredicate, final Term postcondition,
			final Set<Term> oldConjuncts, final Set<Term> postconditionConjuncts) {
		final Set<Term> resultConjuncts = new HashSet<>();
		final IPredicate postcondPred = predFac.newPredicate(postcondition);
		addImplied(services, managedScript, predFac, oldPredicate, oldConjuncts, postconditionConjuncts,
				resultConjuncts);
		addImplied(services, managedScript, predFac, postcondPred, postconditionConjuncts, oldConjuncts,
				resultConjuncts);
		return resultConjuncts;
	}

	public static void addImplied(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predFac, final IPredicate antecedent, final Set<Term> antecedentConjuncts,
			final Set<Term> candidates, final Set<Term> result) {
		final IncrementalImplicationChecker ipc = new IncrementalImplicationChecker(services, managedScript);
		for (final Term candidate : candidates) {
			if (antecedentConjuncts.contains(candidate)) {
				result.add(candidate);
				continue;
			}
			if (!QuantifierUtils.isQuantifierFree(candidate)) {
				continue;
			}
			final BasicPredicate candidatePred = predFac.newPredicate(candidate);
			final Validity val = ipc.checkImplication(antecedent, candidatePred);
			if (val == Validity.VALID) {
				result.add(candidate);
			}
		}
		ipc.releaseLock();
	}

	private static boolean isFalse(final Set<Term> conjuncts) {
		return conjuncts.size() == 1 && SmtUtils.isFalseLiteral(conjuncts.iterator().next());
	}

}
