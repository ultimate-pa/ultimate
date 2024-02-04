/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;

import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessProcedureContract;
import de.uni_freiburg.informatik.ultimate.core.lib.results.InvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ProcedureContractResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class FloydHoareUtils {
	private FloydHoareUtils() {
		// no instances of static class
	}

	public static <LOC extends IcfgLocation> void writeHoareAnnotationToLogger(final IIcfg<LOC> icfg,
			final IFloydHoareAnnotation<LOC> annotation, final ILogger logger, final boolean logTrivialAnnotations) {

		for (final var proc2label2pp : icfg.getProgramPoints().entrySet()) {
			for (final LOC pp : proc2label2pp.getValue().values()) {
				final IPredicate hoare = annotation.getAnnotation(pp);

				if (hoare == null) {
					logger.info("For program point %s no Hoare annotation was computed.", prettyPrintProgramPoint(pp));
				} else if (logTrivialAnnotations || !SmtUtils.isTrueLiteral(hoare.getFormula())) {
					logger.info("At program point %s the Hoare annotation is: %s", prettyPrintProgramPoint(pp),
							hoare.getFormula());
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
			sb.append("(line ");
			sb.append(startLine);
		} else {
			sb.append("(lines ");
			sb.append(startLine);
			sb.append(" ");
			sb.append(endLine);
		}
		sb.append(")");
		return sb.toString();
	}

	public static void createInvariantResults(final String pluginName, final IIcfg<IcfgLocation> icfg,
			final IFloydHoareAnnotation<IcfgLocation> annotation, final IBacktranslationService backTranslatorService,
			final Consumer<InvariantResult<IIcfgElement, Term>> reporter) {
		final Set<IcfgLocation> locsForLoopLocations = new HashSet<>();
		locsForLoopLocations.addAll(IcfgUtils.getPotentialCycleProgramPoints(icfg));
		locsForLoopLocations.addAll(icfg.getLoopLocations());
		// find all locations that have outgoing edges which are annotated with LoopEntry, i.e., all loop candidates

		for (final IcfgLocation locNode : locsForLoopLocations) {
			final IPredicate hoare = annotation.getAnnotation(locNode);
			if (hoare == null) {
				continue;
			}
			final Term formula = hoare.getFormula();
			final InvariantResult<IIcfgElement, Term> invResult =
					new InvariantResult<>(pluginName, locNode, backTranslatorService, formula);
			reporter.accept(invResult);

			if (SmtUtils.isTrueLiteral(formula)) {
				continue;
			}
			// TODO #proofRefactor
			new WitnessInvariant(invResult.getInvariant()).annotate(locNode);
		}
	}

	public static void createProcedureContractResults(final IUltimateServiceProvider services, final String pluginName,
			final IIcfg<IcfgLocation> icfg, final IFloydHoareAnnotation<IcfgLocation> annotation,
			final IBacktranslationService backTranslatorService,
			final Consumer<ProcedureContractResult<IIcfgElement, Term>> reporter) {
		final Map<String, IcfgLocation> exitNodes = icfg.getProcedureExitNodes();
		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		for (final Entry<String, IcfgLocation> e : entryNodes.entrySet()) {
			final String procName = e.getKey();
			if (isAuxiliaryProcedure(procName)) {
				continue;
			}
			final IcfgLocation entry = e.getValue();
			final IcfgLocation exit = exitNodes.get(procName);
			final IPredicate requires = annotation.getAnnotation(entry);
			final IPredicate ensures = annotation.getAnnotation(exit);
			if (ensures != null) {
				final Term ensuresFormula = ensures.getFormula();
				final Term requiresFormula =
						PredicateUtils.eliminateOldVars(services, icfg.getCfgSmtToolkit().getManagedScript(), requires);

				final ProcedureContractResult<IIcfgElement, Term> result = new ProcedureContractResult<>(pluginName,
						exit, backTranslatorService, procName, requiresFormula, ensuresFormula);
				reporter.accept(result);

				// TODO #proofRefactor
				new WitnessProcedureContract(result.getReqiresResult(), result.getEnsuresResult()).annotate(exit);
			}
		}
	}

	private static boolean isAuxiliaryProcedure(final String proc) {
		return "ULTIMATE.init".equals(proc) || "ULTIMATE.start".equals(proc);
	}
}
