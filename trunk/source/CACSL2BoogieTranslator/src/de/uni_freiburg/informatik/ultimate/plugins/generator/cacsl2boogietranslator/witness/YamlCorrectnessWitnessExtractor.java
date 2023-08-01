package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

public class YamlCorrectnessWitnessExtractor extends CorrectnessWitnessExtractor {
	private Witness mWitness;

	public YamlCorrectnessWitnessExtractor(final IUltimateServiceProvider service) {
		super(service);
	}

	public void setWitness(final Witness witness) {
		mWitness = witness;
	}

	@Override
	public boolean isReady() {
		return mWitness != null && mTranslationUnit != null;
	}

	@Override
	protected HashRelation<IASTNode, ExtractedWitnessInvariant> extract() {
		final HashRelation<IASTNode, ExtractedWitnessInvariant> rtr = new HashRelation<>();
		for (final WitnessEntry entry : mWitness.getEntries()) {
			int line = -1;
			if (entry instanceof LocationInvariant && !mCheckOnlyLoopInvariants) {
				line = ((LocationInvariant) entry).getLocation().getLine();
			}
			if (entry instanceof LoopInvariant) {
				line = ((LoopInvariant) entry).getLocation().getLine();
			}
			final LineMatchingVisitor visitor = new LineMatchingVisitor(line);
			visitor.run(mTranslationUnit);
			final Set<IASTNode> matchesBefore = visitor.getMatchedNodesBefore();
			final Set<IASTNode> matchesAfter = visitor.getMatchedNodesAfter();
			if (matchesBefore.isEmpty() && matchesAfter.isEmpty()) {
				mStats.fail();
				continue;
			}
			extractFromEntry(entry, matchesBefore, matchesAfter, rtr);
			mStats.success();
		}

		return rtr;
	}

	private static void extractFromEntry(final WitnessEntry entry, final Set<IASTNode> matchesBefore,
			final Set<IASTNode> matchesAfter, final HashRelation<IASTNode, ExtractedWitnessInvariant> invariants) {
		final Set<String> labels = Set.of(entry.getMetadata().getUuid().toString());
		if (entry instanceof LoopInvariant) {
			final String invariant = ((LoopInvariant) entry).getInvariant().getExpression();
			Stream.concat(matchesBefore.stream(), matchesAfter.stream()).forEach(x -> invariants.addPair(x,
					new ExtractedWitnessInvariant(invariant, labels, x, false, false, true)));
		} else if (entry instanceof LocationInvariant) {
			final String invariant = ((LocationInvariant) entry).getInvariant().getExpression();
			matchesBefore.stream().forEach(x -> invariants.addPair(x,
					new ExtractedWitnessInvariant(invariant, labels, x, true, false, false)));
			matchesAfter.stream().forEach(x -> invariants.addPair(x,
					new ExtractedWitnessInvariant(invariant, labels, x, false, true, false)));
		} else {
			throw new AssertionError("Unknown witness type " + entry.getClass().getSimpleName());
		}
	}

	private static final class LineMatchingVisitor extends ASTGenericVisitor {
		private final Set<IASTNode> mMatchedNodesBefore = new HashSet<>();
		private final Set<IASTNode> mMatchedNodesAfter = new HashSet<>();
		private final int mLine;

		public LineMatchingVisitor(final int line) {
			super(true);
			mLine = line;
		}

		public void run(final IASTTranslationUnit translationUnit) {
			translationUnit.accept(this);
		}

		public Set<IASTNode> getMatchedNodesBefore() {
			return mMatchedNodesBefore;
		}

		public Set<IASTNode> getMatchedNodesAfter() {
			return mMatchedNodesAfter;
		}

		@Override
		protected int genericVisit(final IASTNode node) {
			final IASTFileLocation loc = node.getFileLocation();
			if (loc == null) {
				return PROCESS_CONTINUE;
			}
			// TODO: Check for the column as well (needs some work to extract it from the offset)
			if (mLine == loc.getStartingLineNumber()) {
				mMatchedNodesBefore.add(node);
				// skip the subtree if a match occurred, but continue with siblings.
				return PROCESS_SKIP;
			}
			if (mLine == loc.getEndingLineNumber()) {
				mMatchedNodesAfter.add(node);
				// skip the subtree if a match occurred, but continue with siblings.
				return PROCESS_SKIP;
			}
			return PROCESS_CONTINUE;
		}
	}
}
