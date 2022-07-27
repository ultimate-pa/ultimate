/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

public class SmtParserUtils {
	private SmtParserUtils() {
		// no instances for static class
	}

	public static Term parseWithVariables(final String syntax, final IUltimateServiceProvider services,
			final CfgSmtToolkit csToolkit) {
		return parseWithVariables(syntax, services, csToolkit.getManagedScript(), csToolkit.getSymbolTable());
	}

	public static Term parseWithVariables(final String syntax, final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final IIcfgSymbolTable symbolTable) {
		final var termVars =
				symbolTable.getGlobals().stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		return parseWithVariables(syntax, services, mgdScript, termVars);
	}

	public static Term parseWithVariables(final String syntax, final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final Set<TermVariable> variables) {
		if (variables.isEmpty()) {
			return parse(syntax, services, mgdScript);
		}

		final String template = "(%1$s %2$s)";
		final String declarations = variables.stream().map(tv -> String.format(template, tv.getName(), tv.getSort()))
				.collect(Collectors.joining(" "));
		final String fullSyntax = "(forall (" + declarations + ") " + syntax + ")";

		final QuantifiedFormula quant = (QuantifiedFormula) TermParseUtils.parseTerm(mgdScript.getScript(), fullSyntax);
		return normalize(quant.getSubformula(), services, mgdScript);
	}

	public static Term parse(final String syntax, final IUltimateServiceProvider services,
			final ManagedScript mgdScript) {
		final Term parsed = TermParseUtils.parseTerm(mgdScript.getScript(), syntax);
		return normalize(parsed, services, mgdScript);
	}

	private static Term normalize(final Term term, final IUltimateServiceProvider services,
			final ManagedScript mgdScript) {
		final Term noLet = new FormulaUnLet().transform(term);

		final Term noIte;
		if (SmtSortUtils.isBoolSort(noLet.getSort())) {
			noIte = new IteRemover(mgdScript).transform(noLet);
		} else {
			noIte = noLet;
		}
		return new CommuhashNormalForm(services, mgdScript.getScript()).transform(noIte);
	}
}
