/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Arrays;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieDagSizePrinter;
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
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessAssumption;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLDagSizePrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assertion;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnotStmt;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class ExtractedWitnessInvariant implements IExtractedWitnessEntry {

	private final ILogger mLogger;
	private final String mInvariant;
	private final IASTNode mMatchedAstNode;

	public ExtractedWitnessInvariant(final ILogger logger, final String invariant, final IASTNode match) {
		mLogger = logger;
		mInvariant = invariant;
		mMatchedAstNode = match;
	}

	public String getInvariant() {
		return mInvariant;
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
		return getLocationDescription() + " [L" + getStartline() + "-L" + getEndline() + "] " + mInvariant;
	}

	protected abstract String getLocationDescription();

	protected ExpressionResult instrument(final ILocation loc, final IDispatcher dispatcher,
			final boolean checkValidity) {
		ACSLNode acslNode = null;
		try {
			checkForQuantifiers(mInvariant);
			acslNode = Parser.parseComment("lstart\n assert " + mInvariant + ";", getStartline(), 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(loc,
					String.format("Unable to instrument \"%s\" at %s (%s)", mInvariant, loc, e.getMessageText()));
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
		logDagSizeOfAcslExpression(acslNode);
		final ExpressionResult assertResult = (ExpressionResult) dispatcher.dispatch(acslNode, mMatchedAstNode);
		logDagSizeOfBoogieExpression(assertResult);
		if (checkValidity) {
			return assertResult;
		}
		return new ExpressionResultBuilder(assertResult)
				.resetStatements(AssertReplacer.replaceAsserts(assertResult.getStatements())).build();
	}

	private void logDagSizeOfAcslExpression(final ACSLNode acslNode) {
		if ((acslNode instanceof final CodeAnnotStmt stmt)
				&& (stmt.getCodeStmt() instanceof final Assertion assertion)) {
			mLogger.info("DAG size of ACSL expression of witness invariant %s: %s", mInvariant,
					ACSLDagSizePrinter.print(assertion.getFormula()));
		}
	}

	private void logDagSizeOfBoogieExpression(final ExpressionResult assertResult) {
		for (final Statement statement : assertResult.getStatements()) {
			if (statement instanceof final AssertStatement assertStatement) {
				mLogger.info("DAG size of Boogie expression of witness invariant %s: %s", mInvariant,
						BoogieDagSizePrinter.print(assertStatement.getFormula()));
			}
		}
	}

	/**
	 * Throw Exception if invariant contains quantifiers. It seems like our parser does not support quantifiers yet, For
	 * the moment it seems to be better to crash here in order to get a meaningful error message.
	 */
	private static void checkForQuantifiers(final String invariant) {
		if (invariant.contains("exists") || invariant.contains("forall")) {
			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(),
					"invariant contains quantifiers");
		}
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
