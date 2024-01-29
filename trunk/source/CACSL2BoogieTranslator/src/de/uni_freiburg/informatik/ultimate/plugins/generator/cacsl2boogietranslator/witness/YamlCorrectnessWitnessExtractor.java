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

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LocationInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Witness;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.WitnessEntry;

/**
 * Extract a correctness witness from a YAML-based witness file.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
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
	protected HashRelation<IASTNode, IExtractedWitnessEntry> computeWitnessEntries() {
		final HashRelation<IASTNode, IExtractedWitnessEntry> rtr = new HashRelation<>();
		for (final WitnessEntry entry : mWitness.getEntries()) {
			final int line;
			if (entry instanceof LocationInvariant && !mCheckOnlyLoopInvariants) {
				line = ((LocationInvariant) entry).getLocation().getLine();
			} else if (entry instanceof LoopInvariant) {
				line = ((LoopInvariant) entry).getLocation().getLine();
			} else {
				mStats.fail();
				continue;
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
			final Set<IASTNode> matchesAfter, final HashRelation<IASTNode, IExtractedWitnessEntry> entries) {
		final Set<String> labels = Set.of(entry.getMetadata().getUuid().toString());
		if (entry instanceof LoopInvariant) {
			final String invariant = ((LoopInvariant) entry).getInvariant().getExpression();
			for (final var match : DataStructureUtils.union(matchesBefore, matchesAfter)) {
				final Optional<IExtractedWitnessEntry> optional =
						entries.getImage(match).stream().filter(x -> x instanceof ExtractedLoopInvariant).findAny();
				if (optional.isPresent()) {
					final ExtractedLoopInvariant old = (ExtractedLoopInvariant) optional.get();
					final String newInvariant = conjunctInvariants(old.getInvariant(), invariant);
					final Set<String> newLables = DataStructureUtils.union(old.getNodeLabels(), labels);
					entries.addPair(match, new ExtractedLoopInvariant(newInvariant, newLables, match));
				} else {
					entries.addPair(match, new ExtractedLoopInvariant(invariant, labels, match));
				}
			}
		} else if (entry instanceof LocationInvariant) {
			final String invariant = ((LocationInvariant) entry).getInvariant().getExpression();
			for (final var match : matchesBefore) {
				final Optional<IExtractedWitnessEntry> optional = entries.getImage(match).stream().filter(
						x -> x instanceof ExtractedLocationInvariant && ((ExtractedLocationInvariant) x).isBefore())
						.findAny();
				if (optional.isPresent()) {
					final ExtractedLocationInvariant old = (ExtractedLocationInvariant) optional.get();
					final String newInvariant = conjunctInvariants(old.getInvariant(), invariant);
					final Set<String> newLables = DataStructureUtils.union(old.getNodeLabels(), labels);
					entries.addPair(match, new ExtractedLocationInvariant(newInvariant, newLables, match, true));
				} else {
					entries.addPair(match, new ExtractedLocationInvariant(invariant, labels, match, true));
				}
			}
			for (final var match : matchesAfter) {
				final Optional<IExtractedWitnessEntry> optional = entries.getImage(match).stream().filter(
						x -> x instanceof ExtractedLocationInvariant && !((ExtractedLocationInvariant) x).isBefore())
						.findAny();
				if (optional.isPresent()) {
					final ExtractedLocationInvariant old = (ExtractedLocationInvariant) optional.get();
					final String newInvariant = conjunctInvariants(old.getInvariant(), invariant);
					final Set<String> newLables = DataStructureUtils.union(old.getNodeLabels(), labels);
					entries.addPair(match, new ExtractedLocationInvariant(newInvariant, newLables, match, false));
				} else {
					entries.addPair(match, new ExtractedLocationInvariant(invariant, labels, match, false));
				}
			}
		} else {
			throw new AssertionError("Unknown witness type " + entry.getClass().getSimpleName());
		}
	}

	private static String conjunctInvariants(final String invariant1, final String invariant2) {
		return "(" + invariant1 + ") && (" + invariant2 + ")";
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
