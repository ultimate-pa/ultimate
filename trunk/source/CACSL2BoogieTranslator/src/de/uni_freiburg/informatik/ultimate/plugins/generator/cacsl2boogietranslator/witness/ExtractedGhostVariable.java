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

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Witness entry for the declaration of ghost variables
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedGhostVariable implements IExtractedWitnessDeclaration {
	private final String mVariable;
	private final IASTNode mMatchedAstNode;
	private final String mExpression;
	private final String mType;

	public ExtractedGhostVariable(final String variable, final String expression, final String type,
			final IASTNode match) {
		mVariable = variable;
		mExpression = expression;
		mType = type;
		mMatchedAstNode = match;
	}

	@Override
	public String toString() {
		return "ghost_variable " + mVariable + " = " + mExpression;
	}

	@Override
	public VariableDeclaration getDeclaration(final FlatSymbolTable symbolTable) {
		final var stv = symbolTable.findCSymbol(mMatchedAstNode, mVariable);
		if (stv == null) {
			throw new AssertionError("No declaration was created for the ghost variable " + mVariable);
		}
		return (VariableDeclaration) stv.getBoogieDecl();
	}

	@Override
	public ExpressionResult getInitializationResult(final IDispatcher dispatcher) {
		ACSLNode acslNode = null;
		try {
			acslNode = Parser.parseComment(String.format("lstart\n ghost %s %s = %s;", mType, mVariable, mExpression),
					1, 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(mMatchedAstNode),
					e.getMessageText());
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
		return (ExpressionResult) dispatcher.dispatch(acslNode, mMatchedAstNode);
	}
}
