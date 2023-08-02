package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.Collection;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class ExtractedWitnessInvariant implements IExtractedWitnessEntry {

	private final String mInvariant;
	private final ImmutableSet<String> mNodeLabels;
	private final IASTNode mMatchedAstNode;

	public ExtractedWitnessInvariant(final String invariant, final Collection<String> nodeLabel, final IASTNode match) {
		mInvariant = invariant;
		mNodeLabels = ImmutableSet.copyOf(nodeLabel);
		mMatchedAstNode = match;
	}

	public String getInvariant() {
		return mInvariant;
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

	@Override
	public IASTNode getRelatedAstNode() {
		return mMatchedAstNode;
	}

	@Override
	public String toString() {
		return getLocationDescription() + " [L" + getStartline() + "-L" + getEndline() + "] " + mInvariant;
	}

	protected abstract String getLocationDescription();

	protected ExpressionResult instrument(final ILocation loc, final IDispatcher dispatcher) {
		ACSLNode acslNode = null;
		try {
			checkForQuantifiers(mInvariant);
			acslNode = Parser.parseComment("lstart\n assert " + mInvariant + ";", getStartline(), 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(loc, e.getMessage());
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
		return (ExpressionResult) dispatcher.dispatch(acslNode, mMatchedAstNode);
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
