package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTNode;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class ExtractedWitnessInvariant {

	private final String mInvariant;
	private final Set<String> mNodeLabels;
	private final IASTNode mMatchedAstNode;
	private final boolean mIsBefore;
	private final boolean mIsAfter;
	private final boolean mIsAt;

	public ExtractedWitnessInvariant(final String invariant, final Collection<String> nodeLabel, final IASTNode match,
			final boolean isBefore, final boolean isAfter, final boolean isAt) {
		mInvariant = invariant;
		mNodeLabels = new HashSet<String>();
		mNodeLabels.addAll(nodeLabel);
		mMatchedAstNode = match;
		mIsBefore = isBefore;
		mIsAfter = isAfter;
		mIsAt = isAt;
	}

	public String getInvariant() {
		return mInvariant;
	}

	public Set<String> getNodeLabels() {
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

	public ExtractedWitnessInvariant merge(final ExtractedWitnessInvariant other) {
		if (other == null) {
			return this;
		}
		if (mMatchedAstNode != other.mMatchedAstNode) {
			throw new IllegalArgumentException("Cannot merge WitnessInvariants that are matched to different nodes");
		}
		final StringBuilder newInvariant = new StringBuilder();
		newInvariant.append('(');
		newInvariant.append(mInvariant);
		newInvariant.append(')');
		newInvariant.append("||");
		newInvariant.append('(');
		newInvariant.append(other.mInvariant);
		newInvariant.append(')');

		final Set<String> newNodeLabels = new HashSet<>();
		newNodeLabels.addAll(mNodeLabels);
		newNodeLabels.addAll(other.mNodeLabels);

		return new ExtractedWitnessInvariant(newInvariant.toString(), newNodeLabels, mMatchedAstNode, isBefore(),
				isAfter(), isAt());
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
}
