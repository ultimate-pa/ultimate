/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;

public final class SmtTestGenerationUtils {

	private SmtTestGenerationUtils() {
		// do not instantiate
	}

	/**
	 * @deprecated Superseded by {@link SmtTestGenerationUtils#generateStringForTestfile2}.
	 */
	@Deprecated
	public static String generateStringForTestfile(final Term term) {
		final StringBuilder result = new StringBuilder();
		result.append(System.lineSeparator());
		final Set<Sort> sorts = new HashSet<>();
		final TermVariable[] freeVars = term.getFreeVars();
		for (final TermVariable tv : freeVars) {
			sorts.add(tv.getSort());
		}
		final Map<Sort, String> sortVarMapping = new HashMap<>();
		int counter = 0;
		for (final Sort sort : sorts) {
			final String declaration;
			if (SmtSortUtils.isIntSort(sort)) {
				final String varName = "intSort";
				sortVarMapping.put(sort, varName);
				declaration = String.format("final Sort %s = SmtSortUtils.getIntSort(mMgdScript);", varName);
			} else if (SmtSortUtils.isArraySort(sort)) {
				if (isIntIntArray(sort)) {
					final String varName = "intintArraySort";
					sortVarMapping.put(sort, varName);
					declaration = String.format("final Sort %s = SmtSortUtils.getArraySort(mScript, intSort, intSort);",
							varName);
				} else if (isIntIntIntArray(sort)) {
					final String varName = "intintintArraySort";
					sortVarMapping.put(sort, varName);
					declaration = String.format(
							"final Sort %s = SmtSortUtils.getArraySort(mScript, intSort, SmtSortUtils.getArraySort(mScript, intSort, intSort));",
							varName);
				} else {
					final String varName = "arraySort" + counter;
					counter++;
					sortVarMapping.put(sort, varName);
					declaration = String.format("final Sort %s = SmtSortUtils.getArraySort(...); // %s", varName, sort);
				}
			} else {
				final String varName = "otherSort" + counter;
				counter++;
				sortVarMapping.put(sort, varName);
				declaration = String.format("final Sort %s = // %s", varName, sort);
			}
			result.append(declaration);
			result.append(System.lineSeparator());
		}
		for (final TermVariable tv : freeVars) {
			final String declaration = String.format("mScript.declareFun(\"%s\", new Sort[0], %s);", tv.getName(),
					sortVarMapping.get(tv.getSort()));
			result.append(declaration);
			result.append(System.lineSeparator());
		}
		result.append(String.format("final String formulaAsString = \"%s\";", term.toStringDirect()));
		result.append(System.lineSeparator());
		result.append("final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);");
		return result.toString();
	}


	/**
	 * Hack for generating tests for quantifier elimination. Probably usable for
	 * SMT-based tests in general.
	 */
	public static String generateStringForTestfile2(final Term term) {
		final TermVariable[] freeVars = term.getFreeVars();
		final Set<FunctionSymbol> funSyms = SmtUtils.extractNonTheoryFunctionSymbols(term);
		// collect sorts
		final Set<Sort> sorts = new HashSet<>();
		for (final TermVariable tv : freeVars) {
			sorts.add(tv.getSort());
		}
		for (final FunctionSymbol fun : funSyms) {
			sorts.add(fun.getReturnSort());
			for (final Sort pSort : fun.getParameterSorts()) {
				sorts.add(pSort);
			}
		}

		final Map<Sort, String> sortVarMapping = new HashMap<>();
		final int counter = 0;
		for (final Sort sort : sorts) {
			final String constructionString;
			if (SmtSortUtils.isBoolSort(sort)) {
				constructionString = "SmtSortUtils::getBoolSort";
			} else if (SmtSortUtils.isRealSort(sort)) {
				constructionString = "SmtSortUtils::getRealSort";
			} else if (SmtSortUtils.isIntSort(sort)) {
				constructionString = "SmtSortUtils::getIntSort";
			} else if (SmtSortUtils.isArraySort(sort)) {
				if (isIntIntArray(sort)) {
					constructionString = "QuantifierEliminationTest::constructIntIntArray";
				} else if (isIntIntIntArray(sort)) {
					constructionString = "QuantifierEliminationTest::constructIntIntIntArray";
				} else {
					constructionString = "arraySort" + counter;
				}
			} else {
				constructionString = "otherSort" + counter;
			}
			sortVarMapping.put(sort, constructionString);
		}

		final HashRelation<Sort, TermVariable> sort2TermVariable = new HashRelation<>();
		for (final TermVariable tv : freeVars) {
			sort2TermVariable.addPair(tv.getSort(), tv);
		}
		final HashRelation3<Sort[], Sort, FunctionSymbol> sortFunctionSymbol = new HashRelation3<>();
		for (final FunctionSymbol funSym : funSyms) {
			sortFunctionSymbol.addTriple(funSym.getParameterSorts(), funSym.getReturnSort(), funSym);
		}
		final StringBuilder result = new StringBuilder();
		result.append(System.lineSeparator());

		result.append("\tfinal FunDecl[] funDecls = new FunDecl[] {");
		result.append(System.lineSeparator());

		for (final Entry<Sort, HashSet<TermVariable>> entry : sort2TermVariable.entrySet()) {
			final String idList = entry.getValue().stream().map(x -> ("\"" + x + "\""))
					.collect(Collectors.joining(", "));
			final String sortConstructionString = sortVarMapping.get(entry.getKey());
			final String funDecl = String.format("\t\tnew FunDecl(%s, %s),", sortConstructionString, idList);
			result.append(funDecl);
			result.append(System.lineSeparator());
		}

		for (final Sort[] paramSorts : sortFunctionSymbol.projectToFst()) {
			for (final Sort returnSort : sortFunctionSymbol.projectToSnd(paramSorts)) {
				final String returnSortConstructionString = sortVarMapping.get(returnSort);
				final Set<FunctionSymbol> funs = sortFunctionSymbol.projectToTrd(paramSorts, returnSort);
				final String idList = funs.stream().map(x -> ("\"" + x.getName() + "\""))
						.collect(Collectors.joining(", "));
				if (Arrays.equals(paramSorts, new Sort[0])) {
					final String funDecl = String.format("\t\tnew FunDecl(%s, %s),", returnSortConstructionString,
							idList);
					result.append(funDecl);
					result.append(System.lineSeparator());
				} else {
					throw new UnsupportedOperationException("not yet implemented");
				}
			}
		}

		result.append("\t};");
		result.append(System.lineSeparator());

		result.append(String.format("\tfinal String formulaAsString = \"%s\";", term.toStringDirect()));
		result.append(System.lineSeparator());
		return result.toString();
	}


	private static boolean isIntIntArray(final Sort sort) {
		if (SmtSortUtils.isArraySort(sort)) {
			if (sort.getArguments().length == 2) {
				if (SmtSortUtils.isIntSort(sort.getArguments()[0])) {
					if (SmtSortUtils.isIntSort(sort.getArguments()[1])) {
						return true;
					}
				}
			}
		}
		return false;
	}

	private static boolean isIntIntIntArray(final Sort sort) {
		if (SmtSortUtils.isArraySort(sort)) {
			if (sort.getArguments().length == 2) {
				if (SmtSortUtils.isIntSort(sort.getArguments()[0])) {
					if (isIntIntArray(sort.getArguments()[1])) {
						return true;
					}
				}
			}
		}
		return false;
	}


}
