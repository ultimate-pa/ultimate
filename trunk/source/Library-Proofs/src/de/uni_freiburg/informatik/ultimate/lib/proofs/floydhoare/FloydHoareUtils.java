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

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

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
}
