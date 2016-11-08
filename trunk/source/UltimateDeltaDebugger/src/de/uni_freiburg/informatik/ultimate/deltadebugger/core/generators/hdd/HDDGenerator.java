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
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.Change;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.StringSourceDocument;

class HDDGenerator implements IVariantGenerator {
	private final HDDGeneratorFactory mFactory;
	private final IPassContext mContext;
	private final int mLevel;
	private final ISourceDocument mSource;
	private final List<IPSTNode> mNodes;
	private final List<List<Change>> mChangeGroups;
	private final List<Change> mPersistentChanges;

	HDDGenerator(HDDGeneratorFactory factory, final IPassContext context, final int level, final ISourceDocument source,
			final List<IPSTNode> nodes, final List<List<Change>> changeGroups, final List<Change> persistentChanges) {
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
		final Map<Class<?>, Map<IPSTNode, Change>> deferredChangeMap = new IdentityHashMap<>();
		getStreamOfAllChanges(activeChanges).forEach(change -> {
			change.apply(rewriter);
			if (change.hasDeferredChange()) {
				final Map<IPSTNode, Change> perChangeClassMap =
						deferredChangeMap.computeIfAbsent(change.getClass(), c -> new IdentityHashMap<>());
				change.updateDeferredChange(perChangeClassMap);
			}
		});
		deferredChangeMap.values().stream().flatMap(m -> m.values().stream())
				.forEach(change -> change.apply(rewriter));
		return rewriter.apply();
	}

	@Override
	public List<IChangeHandle> getChanges() {
		return Collections.unmodifiableList(mChangeGroups.get(0));
	}
	
	private List<Change> getMergedPersistentChanges(final List<IChangeHandle> activeChanges) {
		if (activeChanges.isEmpty()) {
			return mPersistentChanges;
		}
		final List<Change> merged = new ArrayList<>(mPersistentChanges.size() + activeChanges.size());
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
		activeChanges.stream().map(c -> ((Change) c).getNode()).forEach(removedNodes::add);
		return mNodes.stream().filter(n -> !removedNodes.contains(n)).collect(Collectors.toList());
	}

	private Stream<Change> getStreamOfAllChanges(final List<IChangeHandle> activeChanges) {
		return Stream.concat(mPersistentChanges.stream(), activeChanges.stream().map(c -> (Change) c));
	}

	@Override
	public Optional<IVariantGenerator> next(final List<IChangeHandle> activeChanges) {
		// Advance to the next group of changes on this level
		if (mChangeGroups.size() > 1) {
			return Optional.of(new HDDGenerator(mFactory, mContext, mLevel, mSource, getRemainingNodes(activeChanges),
					mChangeGroups.subList(1, mChangeGroups.size()), getMergedPersistentChanges(activeChanges)));
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
		return mFactory.createGeneratorForNextLevel(mContext, mLevel, newSource, remainingNodes, Collections.emptyList());
	}

	private List<IPSTNode> collectNodesOnLevel(final IPSTTranslationUnit tu, final int level) {
		final NodeCollector collector = new NodeCollector(level);
		tu.accept(collector);
		return collector.getResult();
	}
	
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
