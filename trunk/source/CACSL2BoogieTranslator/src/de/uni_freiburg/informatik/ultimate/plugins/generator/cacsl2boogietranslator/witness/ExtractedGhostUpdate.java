/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Witness entry for the update of ghost variables
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedGhostUpdate implements IExtractedWitnessEntry {
	private final ImmutableSet<String> mNodeLabels;
	private final IASTNode mMatchedAstNode;
	private final String mStatement;

	public ExtractedGhostUpdate(final String variable, final String expression, final IASTNode match,
			final Collection<String> nodeLabel) {
		mStatement = String.format("%s = %s;", variable, expression);
		mNodeLabels = ImmutableSet.copyOf(nodeLabel);
		mMatchedAstNode = match;
	}

	@Override
	public ImmutableSet<String> getNodeLabels() {
		return mNodeLabels;
	}

	private int getStartline() {
		return mMatchedAstNode.getFileLocation().getStartingLineNumber();
	}

	private int getEndline() {
		return mMatchedAstNode.getFileLocation().getEndingLineNumber();
	}

	public IASTNode getRelatedAstNode() {
		return mMatchedAstNode;
	}

	@Override
	public String toString() {
		return "ghost_update [L" + getStartline() + "-L" + getEndline() + "] " + mStatement;
	}

	protected ExpressionResult instrument(final ILocation loc, final IDispatcher dispatcher) {
		ACSLNode acslNode = null;
		try {
			acslNode = Parser.parseComment("lstart\n ghost " + mStatement, getStartline(), 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(loc, e.getMessageText());
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
		return (ExpressionResult) dispatcher.dispatch(acslNode, mMatchedAstNode);
	}

	@Override
	public ExpressionResult transform(final ILocation loc, final IDispatcher dispatcher,
			final ExpressionResult expressionResult) {
		final ExpressionResult witness = instrument(loc, dispatcher);
		final List<Statement> oldstatements = expressionResult.getStatements();
		List<Statement> newStatements;
		if (oldstatements.isEmpty()) {
			newStatements = List.of(new AtomicStatement(loc, witness.getStatements().toArray(Statement[]::new)));
		} else {
			final int size = witness.getStatements().size();
			final Statement[] block = witness.getStatements().toArray(new Statement[size + 1]);
			block[size] = oldstatements.get(0);
			newStatements = DataStructureUtils.concat(List.of(new AtomicStatement(loc, block)),
					oldstatements.subList(1, oldstatements.size()));
		}
		return new ExpressionResultBuilder(expressionResult).resetStatements(newStatements).build();
	}
}
