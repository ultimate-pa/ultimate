/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostDeclaration;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessGhostUpdate;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ThreadModularPrePostSpecification;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Provides utility functionalities related to Owicki-Gries proofs.
 */
public class OwickiGriesUtils {
	/**
	 * Constructs the default specification for Petri programs: from the initial marking, no accepting place is
	 * reachable.
	 *
	 * @param <L>
	 *            the type of actions in the Petri program
	 * @param <P>
	 *            the type of places in the Petri program
	 * @param net
	 *            the Petri net
	 * @param factory
	 *            the predicate factory to use for the specification
	 * @return the thread-modular specification as described above
	 */
	public static <L, P> ThreadModularPrePostSpecification<P, Marking<P>>
			getSpecificationForPetriNet(final IPetriNet<L, P> net, final BasicPredicateFactory factory) {
		final var preconditions = Map.of(Marking.initial(net), factory.and());
		return new ThreadModularPrePostSpecification<>(preconditions, net::isAccepting, factory.or());
	}

	public static <L extends IIcfgTransition<?>> void createResultsAndAnnotateIcfg(
			final IUltimateServiceProvider services, final String pluginName, final IIcfg<IcfgLocation> icfg,
			final OwickiGriesAnnotation<L, IcfgLocation, List<IcfgLocation>> annotation,
			final IBacktranslationService backTranslatorService, final Consumer<IResult> reporter) {
		final var logger = services.getLoggingService().getLogger(OwickiGriesUtils.class);

		final Set<IProgramVar> failedGhosts = new HashSet<>();
		final Map<IProgramVar, String> declaredGhosts = new HashMap<>();

		// Process declarations and initial values of ghost variables.
		final var ghostsInits = new HashMap<String, Object>();
		for (final var entry : annotation.getGhostAssignment().entrySet()) {
			final var ghost = entry.getKey();
			final var expr = entry.getValue();

			final var initialValue = backTranslatorService.translateExpression(expr, Term.class);
			if (initialValue == null) {
				logger.warn("Could not translate initial value of ghost variable %s: %s", ghost, initialValue);
				failedGhosts.add(ghost);
				continue;
			}

			final var declaredGhost = backTranslatorService.declareAndTranslateAuxiliaryVariable(ghost.getTerm());
			final var declaredGhostName = backTranslatorService.targetExpressionToString(declaredGhost);
			ghostsInits.put(declaredGhostName, initialValue);
			declaredGhosts.put(ghost, declaredGhostName);
		}
		new WitnessGhostDeclaration<>(ghostsInits).annotate(icfg);

		// Process ghost updates
		for (final var entry : annotation.getAssignmentMapping().entrySet()) {
			final var edge = (IIcfgTransition<?>) entry.getKey();
			final GhostUpdate update = entry.getValue();

			final Map<Object, Object> ghostUpdate = new HashMap<>();
			final Map<String, String> ghostUpdate2 = new HashMap<>();
			for (final var ghost : update.getAssignedVariables()) {
				if (failedGhosts.contains(ghost)) {
					continue;
				}

				final var context = ILocation.getAnnotation(edge);
				final var translatedGhost =
						backTranslatorService.translateExpressionWithContext(ghost.getTerm(), context, Term.class);

				final var term = update.getExpressionFor(ghost);
				final var expression = backTranslatorService.translateExpressionWithContext(term, context, Term.class);
				if (expression == null) {
					logger.warn("Could not translate assignment to ghost variable %s: %s", translatedGhost, term);
					failedGhosts.add(ghost);
				} else {
					ghostUpdate.put(declaredGhosts.get(ghost), expression);
					ghostUpdate2.put(backTranslatorService.targetExpressionToString(translatedGhost),
							backTranslatorService.targetExpressionToString(expression));
				}
			}
			new WitnessGhostUpdate<>(ghostUpdate).annotate(edge);

			final ILocation preLoc = ILocation.getAnnotation(edge.getSource());
			final ILocation postLoc = ILocation.getAnnotation(edge.getTarget());
			logger.info("ghost update for edge from line %2d (col. %2d) to line %2d (col. %2d) is %s",
					preLoc.getStartLine(), preLoc.getStartColumn(), postLoc.getStartLine(), postLoc.getStartColumn(),
					ghostUpdate2);

			try {
				final var edgeTranslated =
						backTranslatorService.translateTrace(List.of((IcfgEdge) edge), IcfgEdge.class);
				logger.info("  " + edgeTranslated.stream().map(e -> BoogiePrettyPrinter.print((Statement) e))
						.collect(Collectors.joining("; ")));
			} catch (final Throwable e) {
				logger.warn(e.getMessage());
			}
		}

		// Process location invariants.
		final var failedGhostTvs = failedGhosts.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		for (final var entry : annotation.getFormulaMapping().entrySet()) {
			final IcfgLocation loc = entry.getKey();
			final Term formula = entry.getValue().getFormula();
			final Object invariant = backTranslatorService.translateExpressionWithContext(formula,
					ILocation.getAnnotation(loc), Term.class);
			final String invariantString =
					invariant == null ? null : backTranslatorService.targetExpressionToString(invariant);

			if (invariant == null || invariant.toString().equals("1")) {
				continue;
			}

			final var invResult = new InvariantResult<>(pluginName, loc, invariant, invariantString, null /* TODO */);
			reporter.accept(invResult);

			final var failedGhost = Arrays.stream(formula.getFreeVars()).filter(failedGhostTvs::contains).findAny();
			if (failedGhost.isPresent()) {
				logger.warn("Invariant contains ghost variable that was not properly backtranslated. "
						+ "Invariant: %s. Ghost variable: %s", invariant, failedGhost.get());
			}
			new WitnessInvariant<>(invariant).annotate(loc);
		}
	}
}
