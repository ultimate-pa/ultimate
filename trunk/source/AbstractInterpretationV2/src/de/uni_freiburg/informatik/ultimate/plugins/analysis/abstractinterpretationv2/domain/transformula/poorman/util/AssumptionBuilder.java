/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

public class AssumptionBuilder {

	/**
	 * Constructs a Boogie {@link AssumeStatement} in which the given term is converted into an assume statement.
	 *
	 * @param logger
	 *            The current logger object.
	 * @param term
	 *            The term to construct an assume statement for.
	 * @param variableRetainmentSet
	 *            The set of variables whose names should be looked up in the temporary variable set of the symbol table
	 *            instead of the Boogie symbol table itself.
	 * @param alternateOldNames
	 *            The renamed old variables.
	 * @param mappedTerm2Expression
	 *            The mapped term2Expression object that can handle omitted variables in the Boogie symbol table.
	 * @return An {@link AssumeStatement} containing the conversion of the term to an assume statement.
	 */
	public static AssumeStatement[] constructBoogieAssumeStatement(final ILogger logger,
			final Set<TermVariable> variableRetainmentSet, final Map<TermVariable, String> alternateOldNames,
			final MappedTerm2Expression mappedTerm2Expression, final Term... terms) {
		final List<AssumeStatement> assumes = new ArrayList<>();

		for (final Term term : terms) {
			final Expression termExpression =
					mappedTerm2Expression.translate(term, variableRetainmentSet, alternateOldNames);
			assumes.add(new AssumeStatement(termExpression.getLoc(), termExpression));
		}

		if (logger.isDebugEnabled()) {
			logger.debug(
					"Terms: " + Arrays.stream(terms).map(term -> term.toString()).collect(Collectors.joining(", ")));
			logger.debug("Constructed assume expressions: " + assumes.stream()
					.map(assume -> BoogiePrettyPrinter.print(assume.getFormula())).collect(Collectors.joining(", ")));
		}

		return assumes.toArray(new AssumeStatement[assumes.size()]);
	}

	/**
	 * Converts multiple statements to a Boogie {@link CodeBlock}.
	 *
	 * @param codeBlockFactory
	 *            The {@link CodeBlockFactory} to construct the {@link CodeBlock} with.
	 * @param statements
	 *            The list of statements to use.
	 * @return A new {@link CodeBlock} representing the list of statements.
	 */
	public static CodeBlock constructCodeBlock(final CodeBlockFactory codeBlockFactory, final Statement... statements) {
		final List<Statement> statementList =
				Arrays.stream(statements).filter(stmt -> stmt != null).collect(Collectors.toList());
		return codeBlockFactory.constructStatementSequence(null, null, statementList, Origin.IMPLEMENTATION);
	}
}
