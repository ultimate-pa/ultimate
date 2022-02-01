/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.StringSourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.util.ListUtils;

/**
 * Generator for hierarchical delta debugging.
 */
class HddGenerator implements IVariantGenerator {
	private final HddGeneratorFactory mFactory;
	private final IPassContext mContext;
	private final int mLevel;
	private final ISourceDocument mSource;
	private final List<IPSTNode> mNodes;
	private final List<List<HddChange>> mChangeGroups;
	private final List<HddChange> mPersistentChanges;
	
	HddGenerator(final HddGeneratorFactory factory, final IPassContext context, final int level,
			final ISourceDocument source, final List<IPSTNode> nodes, final List<List<HddChange>> changeGroups,
			final List<HddChange> persistentChanges) {
		mFactory = factory;
		mContext = context;
		mLevel = level;
		mSource = source;
		mNodes = Collections.unmodifiableList(nodes);
		mChangeGroups = Collections.unmodifiableList(changeGroups);
		mPersistentChanges = Collections.unmodifiableList(persistentChanges);
	}
	
	@Override
	public String apply(final List<IChangeHandle> activeChanges) {
		final SourceRewriter rewriter = new SourceRewriter(mSource);
		final Map<Class<?>, Map<IPSTNode, HddChange>> deferredChangeMap = new IdentityHashMap<>();
		getStreamOfAllChanges(activeChanges).forEach(change -> {
			change.apply(rewriter);
			if (change.hasDeferredChange()) {
				final Map<IPSTNode, HddChange> perChangeClassMap =
						deferredChangeMap.computeIfAbsent(change.getClass(), c -> new IdentityHashMap<>());
				change.updateDeferredChange(perChangeClassMap);
			}
		});
		deferredChangeMap.values().stream().flatMap(m -> m.values().stream()).forEach(change -> change.apply(rewriter));
		return rewriter.apply();
	}
	
	@Override
	public List<IChangeHandle> getChanges() {
		return Collections.unmodifiableList(mChangeGroups.get(0));
	}
	
	private List<HddChange> createAlternativeChanges(final List<IChangeHandle> activeChanges, final List<HddChange> allChanges) {
		final List<HddChange> alternativeChanges = ListUtils.complementOfSubsequence(activeChanges, allChanges).stream()
				.map(c -> ((HddChange) c).createAlternativeChange()).filter(Optional::isPresent).map(Optional::get)
				.collect(Collectors.toList());
		IntStream.range(0, alternativeChanges.size()).forEach(i -> alternativeChanges.get(i).setSequenceIndex(i));
		return Collections.unmodifiableList(alternativeChanges);
	}
	
	private List<List<HddChange>> getNextChangeGroups(final List<IChangeHandle> activeChanges) {
		// Check for alternative changes for the inactive changes of the current group
		final List<HddChange> alternativeChanges = createAlternativeChanges(activeChanges, mChangeGroups.get(0));
		if (!alternativeChanges.isEmpty()) {
			final List<List<HddChange>> nextChangeGroups = new ArrayList<>(mChangeGroups);
			nextChangeGroups.set(0, alternativeChanges);
			return Collections.unmodifiableList(nextChangeGroups);
		}
		return mChangeGroups.subList(1, mChangeGroups.size());
	}
	
	private List<HddChange> getMergedPersistentChanges(final List<IChangeHandle> activeChanges) {
		if (activeChanges.isEmpty()) {
			return mPersistentChanges;
		}
		final List<HddChange> merged = new ArrayList<>(mPersistentChanges.size() + activeChanges.size());
		getStreamOfAllChanges(activeChanges).forEachOrdered(merged::add);
		merged.sort(Comparator.comparingInt(c -> c.getNode().offset()));
		return merged;
	}
	
	private List<IPSTNode> getRemainingNodes(final List<IChangeHandle> activeChanges) {
		if (activeChanges.isEmpty()) {
			return mNodes;
		}
		// Compute the remaining nodes by removing nodes that have been
		// successfully changed
		final Set<IPSTNode> removedNodes = Collections.newSetFromMap(new IdentityHashMap<>(activeChanges.size()));
		activeChanges.stream().map(c -> ((HddChange) c).getNode()).forEach(removedNodes::add);
		return mNodes.stream().filter(n -> !removedNodes.contains(n)).collect(Collectors.toList());
	}
	
	private Stream<HddChange> getStreamOfAllChanges(final List<IChangeHandle> activeChanges) {
		return Stream.concat(mPersistentChanges.stream(), activeChanges.stream().map(c -> (HddChange) c));
	}
	
	@Override
	public Optional<IVariantGenerator> next(final List<IChangeHandle> activeChanges) {
		// Advance to the next group of changes on this level
		final List<List<HddChange>> nextChangeGroups = getNextChangeGroups(activeChanges);
		if (!nextChangeGroups.isEmpty()) {
			return Optional.of(new HddGenerator(mFactory, mContext, mLevel, mSource, getRemainingNodes(activeChanges),
					nextChangeGroups, getMergedPersistentChanges(activeChanges)));
		}

		// Continue with the remaining nodes without reparsing
		if (!mFactory.isReparseBetweenLevelsEnabled()) {
			return mFactory.createGeneratorForNextLevel(mContext, mLevel, mSource, getRemainingNodes(activeChanges),
					getMergedPersistentChanges(activeChanges));
		}
		
		// Skip reparsing if no changes could be applied
		if (activeChanges.isEmpty() && mPersistentChanges.isEmpty()) {
			return mFactory.createGeneratorForNextLevel(mContext, mLevel, mSource, mNodes, mPersistentChanges);
		}
		
		// Unparse, parse, and collect nodes on the current level
		final ISourceDocument newSource = new StringSourceDocument(apply(activeChanges));
		final IASTTranslationUnit ast = mContext.getParser().parse(newSource.getText());
		final IPSTTranslationUnit tu = mContext.getParser().createPst(ast, newSource);
		final List<IPSTNode> remainingNodes = collectNodesOnLevel(tu, mLevel);
		return mFactory.createGeneratorForNextLevel(mContext, mLevel, newSource, remainingNodes,
				Collections.emptyList());
	}
	
	private List<IPSTNode> collectNodesOnLevel(final IPSTTranslationUnit translationUnit, final int level) {
		final NodeCollector collector = new NodeCollector(level);
		translationUnit.accept(collector);
		return collector.getResult();
	}
	
	/**
	 * Collector of PST nodes.
	 */
	private final class NodeCollector implements IPSTVisitor {
		private final List<IPSTNode> mResult = new ArrayList<>();
		private final int mTargetLevel;
		private int mCurrentLevel;
		
		NodeCollector(final int targetLevel) {
			mTargetLevel = targetLevel;
		}
		
		@Override
		public int defaultLeave(final IPSTNode node) {
			--mCurrentLevel;
			return PROCESS_CONTINUE;
		}
		
		@Override
		public int defaultVisit(final IPSTNode node) {
			if (mFactory.getStrategy().skipSubTree(node)) {
				return PROCESS_SKIP;
			}
			if (mCurrentLevel == mTargetLevel) {
				mResult.add(node);
				return PROCESS_SKIP;
			}
			++mCurrentLevel;
			return PROCESS_CONTINUE;
		}
		
		public List<IPSTNode> getResult() {
			return mResult;
		}
	}
}
