/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.SkipResult;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessAssumption;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Class for extracted function contracts, which allows their instrumentation via ACSL.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedFunctionContract {
	private final String mRequires;
	private final String mEnsures;
	private final IASTNode mMatchedNode;

	public ExtractedFunctionContract(final String requires, final String ensures, final IASTNode matchedNode) {
		mRequires = requires;
		mEnsures = ensures;
		mMatchedNode = matchedNode;
	}

	private int getStartLine() {
		return mMatchedNode.getFileLocation().getStartingLineNumber();
	}

	@Override
	public String toString() {
		return "Function contract at [L" + getStartLine() + "]: requires " + mRequires + ", ensures " + mEnsures;
	}

	private ACSLNode parseString(final ILocation loc, final String string) {
		try {
			return Parser.parseComment("gstart\n " + string + ";", getStartLine(), 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(loc,
					String.format("Cannot parse contract \"%s\" at %s (%s)", string, loc, e.getMessageText()));
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
	}

	public Result getRequiresHint(final IDispatcher dispatcher, final IASTNode node) {
		if (mRequires == null) {
			return new SkipResult();
		}
		return instrumentAsHint(dispatcher, mRequires, node);
	}

	public Result getEnsuresHint(final IDispatcher dispatcher, final IASTNode node) {
		if (mEnsures == null) {
			return new SkipResult();
		}
		return instrumentAsHint(dispatcher, mEnsures, node);
	}

	private static ExpressionResult instrumentAsHint(final IDispatcher dispatcher, final String contract,
			final IASTNode node) {
		final ILocation loc = LocationFactory.createIgnoreCLocation(node);
		ACSLNode acslNode = null;
		try {
			acslNode = Parser.parseComment("lstart\n assert " + contract + ";",
					node.getFileLocation().getStartingLineNumber(), 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(loc,
					String.format("Unable to instrument \"%s\" at %s (%s)", contract, loc, e.getMessageText()));
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
		final ExpressionResult assertResult = (ExpressionResult) dispatcher.dispatch(acslNode, node);
		return new ExpressionResultBuilder(assertResult)
				.resetStatements(AssertReplacer.replaceAsserts(assertResult.getStatements())).build();
	}

	public List<ACSLNode> getAcslContractClauses() {
		final List<ACSLNode> result = new ArrayList<>();
		final ILocation loc = LocationFactory.createIgnoreCLocation(mMatchedNode);
		if (mRequires != null) {
			result.add(parseString(loc, "requires " + mRequires));
		}
		if (mEnsures != null) {
			result.add(parseString(loc, "ensures " + mEnsures));
		}
		return result;
	}

	private static final class AssertReplacer extends BoogieTransformer {
		public static List<Statement> replaceAsserts(final List<Statement> statements) {
			return Arrays.asList(new AssertReplacer().processStatements(statements.toArray(Statement[]::new)));
		}

		@Override
		protected Statement processStatement(final Statement statement) {
			if (statement instanceof final AssertStatement assertSt) {
				final Expression assertion = assertSt.getFormula();
				final ILocation loc = assertSt.getLocation();
				final Statement assumption = new AssumeStatement(loc, assertion);
				new WitnessAssumption(false).annotate(assumption);
				final Statement negatedAssumption = new AssumeStatement(loc, ExpressionFactory.not(loc, assertion));
				new WitnessAssumption(true).annotate(negatedAssumption);
				return new IfStatement(loc, new WildcardExpression(loc, BoogieType.TYPE_BOOL),
						new Statement[] { assumption }, new Statement[] { negatedAssumption });
			}
			return super.processStatement(statement);
		}
	}
}
