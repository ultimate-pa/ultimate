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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.LineOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.witnessparser.yaml.Location;
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
		// TODO: The column extraction happens in LocationFactory, so we create one as a workaround
		final LocationFactory locationFactory =
				new LocationFactory(null, new LineOffsetComputer(mTranslationUnit.getRawSignature()));
		final Map<IASTNode, ExtractedLoopInvariant> loopInvariants = new HashMap<>();
		final Map<IASTNode, ExtractedLocationInvariant> locationInvariantsBefore = new HashMap<>();
		final Map<IASTNode, ExtractedLocationInvariant> locationInvariantsAfter = new HashMap<>();
		final HashRelation<IASTNode, IExtractedWitnessEntry> rtr = new HashRelation<>();
		for (final WitnessEntry entry : mWitness.getEntries()) {
			final Location location;
			final BiConsumer<IASTNode, Boolean> addFunction;
			if (entry instanceof LocationInvariant) {
				if (mCheckOnlyLoopInvariants) {
					continue;
				}
				location = ((LocationInvariant) entry).getLocation();
				addFunction = (node, before) -> addLocationInvariant((LocationInvariant) entry, node,
						Boolean.TRUE.equals(before) ? locationInvariantsBefore : locationInvariantsAfter, before);
			} else if (entry instanceof LoopInvariant) {
				location = ((LoopInvariant) entry).getLocation();
				addFunction = (node, before) -> addLoopInvariant((LoopInvariant) entry, node, loopInvariants);
			} else {
				throw new UnsupportedOperationException("Unknown entry type " + entry.getClass().getSimpleName());
			}
			final LineColumnMatchingVisitor visitor = new LineColumnMatchingVisitor(location, locationFactory);
			visitor.run(mTranslationUnit);
			final Set<IASTNode> matchesBefore = visitor.getMatchedNodesBefore();
			final Set<IASTNode> matchesAfter = visitor.getMatchedNodesAfter();
			if (matchesBefore.isEmpty() && matchesAfter.isEmpty()) {
				if (mIgnoreUnmatchedEntries) {
					mStats.fail();
					continue;
				}
				throw new UnsupportedOperationException("The witness entry " + entry + " could not be matched.");
			}
			matchesBefore.forEach(x -> addFunction.accept(x, true));
			matchesAfter.forEach(x -> addFunction.accept(x, false));
			mStats.success();
		}
		loopInvariants.forEach(rtr::addPair);
		locationInvariantsBefore.forEach(rtr::addPair);
		locationInvariantsAfter.forEach(rtr::addPair);
		return rtr;
	}

	private static void addLocationInvariant(final LocationInvariant current, final IASTNode node,
			final Map<IASTNode, ExtractedLocationInvariant> locationInvariants, final boolean isBefore) {
		String invariant = current.getInvariant().getExpression();
		Set<String> labels = Set.of(current.getMetadata().getUuid().toString());
		final ExtractedLocationInvariant old = locationInvariants.get(node);
		if (old != null) {
			invariant = conjunctInvariants(old.getInvariant(), invariant);
			labels = DataStructureUtils.union(old.getNodeLabels(), labels);
		}
		locationInvariants.put(node, new ExtractedLocationInvariant(invariant, labels, node, isBefore));
	}

	private static void addLoopInvariant(final LoopInvariant current, final IASTNode node,
			final Map<IASTNode, ExtractedLoopInvariant> loopInvariants) {
		String invariant = current.getInvariant().getExpression();
		Set<String> labels = Set.of(current.getMetadata().getUuid().toString());
		final ExtractedLoopInvariant old = loopInvariants.get(node);
		if (old != null) {
			invariant = conjunctInvariants(old.getInvariant(), invariant);
			labels = DataStructureUtils.union(old.getNodeLabels(), labels);
		}
		loopInvariants.put(node, new ExtractedLoopInvariant(invariant, labels, node));
	}

	private static String conjunctInvariants(final String invariant1, final String invariant2) {
		return "(" + invariant1 + ") && (" + invariant2 + ")";
	}

	private static final class LineColumnMatchingVisitor extends ASTGenericVisitor {
		private final Set<IASTNode> mMatchedNodesBefore = new HashSet<>();
		private final Set<IASTNode> mMatchedNodesAfter = new HashSet<>();
		private final Location mLocation;
		private final LocationFactory mLocationFactory;

		public LineColumnMatchingVisitor(final Location location, final LocationFactory locationFactory) {
			super(true);
			mLocation = location;
			mLocationFactory = locationFactory;
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
			final ILocation loc = mLocationFactory.createCLocation(node);
			if (loc == null) {
				return PROCESS_CONTINUE;
			}
			// TODO: Be more generous about matching columns (e.g. whitespaces between nodes)?
			if (mLocation.getLine() == loc.getStartLine() && mLocation.getColumn() == loc.getStartColumn()) {
				mMatchedNodesBefore.add(node);
				// skip the subtree if a match occurred, but continue with siblings.
				return PROCESS_SKIP;
			}
			if (mLocation.getLine() == loc.getEndLine() && mLocation.getColumn() == loc.getEndColumn()) {
				mMatchedNodesAfter.add(node);
				// skip the subtree if a match occurred, but continue with siblings.
				return PROCESS_SKIP;
			}
			return PROCESS_CONTINUE;
		}
	}
}
