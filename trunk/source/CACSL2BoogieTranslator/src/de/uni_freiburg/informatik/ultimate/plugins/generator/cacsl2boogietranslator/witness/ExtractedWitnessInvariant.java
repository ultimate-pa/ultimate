package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ExtractedWitnessInvariant {

	private final String mInvariant;
	private final ImmutableSet<String> mNodeLabels;
	private final IASTNode mMatchedAstNode;
	private final boolean mIsBefore;
	private final boolean mIsAfter;
	private final boolean mIsAt;

	public ExtractedWitnessInvariant(final String invariant, final Collection<String> nodeLabel, final IASTNode match,
			final boolean isBefore, final boolean isAfter, final boolean isAt) {
		mInvariant = invariant;
		mNodeLabels = ImmutableSet.copyOf(nodeLabel);
		mMatchedAstNode = match;
		mIsBefore = isBefore;
		mIsAfter = isAfter;
		mIsAt = isAt;
	}

	public String getInvariant() {
		return mInvariant;
	}

	public ImmutableSet<String> getNodeLabels() {
		return mNodeLabels;
	}

	public int getStartline() {
		return mMatchedAstNode.getFileLocation().getStartingLineNumber();
	}

	public int getEndline() {
		return mMatchedAstNode.getFileLocation().getEndingLineNumber();
	}

	public boolean isBefore() {
		return mIsBefore;
	}

	public boolean isAfter() {
		return mIsAfter;
	}

	public boolean isAt() {
		return mIsAt;
	}

	public IASTNode getRelatedAstNode() {
		return mMatchedAstNode;
	}

	@Override
	public String toString() {
		return getBAACode() + " [L" + getStartline() + "-L" + getEndline() + "] " + mInvariant;
	}

	public String toStringWithCNode() {
		return toString() + " --- " + getRelatedAstNode().getRawSignature();
	}

	public String toStringWithWitnessNodeLabel() {
		return getBAACode() + " [L" + getStartline() + "-L" + getEndline() + "]["
				+ mNodeLabels.stream().collect(Collectors.joining(", ")) + "]" + mInvariant;
	}

	/**
	 * @return A string of the form "(baa)" where b is either 0 or 1 and encodes the value of before, at, and after.
	 *         E.g., (010) means before=false, at=true, after=false.
	 */
	private String getBAACode() {
		final StringBuilder sb = new StringBuilder(5);
		sb.append('(');
		sb.append(isBefore() ? '1' : '0');
		sb.append(isAt() ? '1' : '0');
		sb.append(isAfter() ? '1' : '0');
		sb.append(')');
		return sb.toString();
	}

	public ExpressionResult transform(final ILocation loc, final IDispatcher dispatcher,
			final ExpressionResult expressionResult) {
		ACSLNode acslNode = null;
		try {
			checkForQuantifiers(mInvariant);
			acslNode = Parser.parseComment("lstart\n assert " + mInvariant + ";", getStartline(), 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(loc, e.getMessage());
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
		final Result invariantResult = dispatcher.dispatch(acslNode, mMatchedAstNode);
		if (!(invariantResult instanceof ExpressionResult)) {
			return null;
		}
		final ExpressionResult invariantExprResult = (ExpressionResult) invariantResult;
		if (isBefore()) {
			return new ExpressionResultBuilder(invariantExprResult).addAllIncludingLrValue(expressionResult).build();
		}
		if (isAfter()) {
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValue(invariantExprResult).build();
		}
		if (isAt()) {
			final List<Statement> statements = new ArrayList<>();
			boolean hasLoop = false;
			for (final Statement st : expressionResult.getStatements()) {
				if (st instanceof WhileStatement) {
					assert !hasLoop;
					hasLoop = true;
					final WhileStatement whileOld = (WhileStatement) st;
					statements.add(new WhileStatement(loc, whileOld.getCondition(), DataStructureUtils
							.concat(whileOld.getInvariants(), extractLoopInvariants(invariantExprResult, loc)),
							whileOld.getBody()));
				} else {
					statements.add(st);
				}
			}
			if (hasLoop) {
				return new ExpressionResultBuilder(expressionResult).resetStatements(statements).build();
			}
			return new ExpressionResultBuilder(invariantExprResult).addAllIncludingLrValue(expressionResult).build();
		}
		throw new AssertionError("Invariant does not belong to any location.");
	}

	private static LoopInvariantSpecification[] extractLoopInvariants(final ExpressionResult result,
			final ILocation loc) {
		final List<LoopInvariantSpecification> specs = new ArrayList<>();
		for (final Statement st : result.getStatements()) {
			if (st instanceof AssertStatement) {
				final LoopInvariantSpecification spec =
						new LoopInvariantSpecification(loc, false, ((AssertStatement) st).getFormula());
				final Check check = new Check(Check.Spec.WITNESS_INVARIANT);
				check.annotate(spec);
				specs.add(spec);
			} else {
				throw new AssertionError(st.getClass().getSimpleName() + " is not supported as annotation of a loop.");
			}
		}
		return specs.toArray(LoopInvariantSpecification[]::new);
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
}
