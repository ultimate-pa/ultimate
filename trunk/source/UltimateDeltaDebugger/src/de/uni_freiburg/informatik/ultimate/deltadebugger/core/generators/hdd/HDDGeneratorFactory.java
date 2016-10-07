package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd;

import java.util.ArrayList;
import java.util.Arrays;
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

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.ChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.VariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.ChangeGenerator.ExpansionResult;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.Change;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.StringSourceDocument;

public class HDDGeneratorFactory {
	
	private final HDDStrategy strategy;
	private final boolean reparseBetweenLevels;
	
	public HDDGeneratorFactory() {
		strategy = new DefaultStrategy();
		reparseBetweenLevels = false;
	}
	
	public HDDGeneratorFactory(HDDStrategy strategy, boolean reparseBetweenLevels) {
		this.strategy = strategy;
		this.reparseBetweenLevels = reparseBetweenLevels;
	}

	public Optional<VariantGenerator> analyze(PassContext context) {
		return createGeneratorForNextLevel(context, 0, context.getInput(), Arrays.asList(context.getSharedPST()),
				Collections.emptyList());
	}
	
	private Optional<VariantGenerator> createGeneratorForNextLevel(PassContext context, int currentLevel,
			ISourceDocument source, List<IPSTNode> nodes, List<Change> persistentChanges) {
		final ChangeGenerator changeGenerator = new ChangeGenerator(strategy);
		ExpansionResult expansion = changeGenerator.generateNextLevelChanges(nodes);
		if (expansion.changeGroups.isEmpty()) {
			return Optional.empty();
		}
		return Optional.of(new Generator(context, currentLevel + expansion.advancedLevels, source,
				expansion.remainingNodes, expansion.changeGroups, persistentChanges));
	}
	
	private class Generator implements VariantGenerator {
		final PassContext context;
		final int level;
		final ISourceDocument source;
		final List<IPSTNode> nodes;
		final List<List<Change>> changeGroups;
		final List<Change> persistentChanges;
		
		Generator(PassContext context, int level, ISourceDocument source, List<IPSTNode> nodes, List<List<Change>> changeGroups,
				List<Change> persistentChanges) {
			this.context = context;
			this.level = level;
			this.source = source;
			this.nodes = Collections.unmodifiableList(nodes);
			this.changeGroups = Collections.unmodifiableList(changeGroups);
			this.persistentChanges = Collections.unmodifiableList(persistentChanges);
		}
		
		@Override
		public List<ChangeHandle> getChanges() {
			return Collections.unmodifiableList(changeGroups.get(0));
		}

		@Override
		public String apply(List<ChangeHandle> activeChanges) {
			final SourceRewriter rewriter = new SourceRewriter(source);
			final Map<Class<?>, Map<IPSTNode, Change>> deferredChangeMap = new IdentityHashMap<>();
			getStreamOfAllChanges(activeChanges).forEach(change -> {
				change.apply(rewriter);
				if (change.hasDeferredChange()) {
					Map<IPSTNode, Change> perChangeClassMap = deferredChangeMap.computeIfAbsent(change.getClass(),
							c -> new IdentityHashMap<>());
					change.updateDeferredChange(perChangeClassMap);
				}
			});
			deferredChangeMap.values().stream().flatMap(m -> m.values().stream())
					.forEach(change -> change.apply(rewriter));
			return rewriter.apply();
		}
		
		@Override
		public Optional<VariantGenerator> next(List<ChangeHandle> activeChanges) {
			// Advance to the next group of changes on this level
			if (changeGroups.size() > 1) {
				return Optional.of(new Generator(context, level, source, getRemainingNodes(activeChanges),
						changeGroups.subList(1, changeGroups.size()), getMergedPersistentChanges(activeChanges)));
			}

			// Continue with the remaining nodes without reparsing
			if (!reparseBetweenLevels) {
				return createGeneratorForNextLevel(context, level, source, getRemainingNodes(activeChanges),
						getMergedPersistentChanges(activeChanges));
			}
			
			// Skip reparsing if no changes could be applied
			if (activeChanges.isEmpty() && persistentChanges.isEmpty()) {
				return createGeneratorForNextLevel(context, level, source, nodes, persistentChanges);
			}
		
			// Unparse, parse, and collect nodes on the current level
			final ISourceDocument newSource = new StringSourceDocument(apply(activeChanges));
			final IASTTranslationUnit ast = context.getParser().parse(newSource.getText());
			final IPSTTranslationUnit tu = context.getParser().createPST(ast, newSource);
			final List<IPSTNode> remainingNodes = collectNodesOnLevel(tu, level);
			return createGeneratorForNextLevel(context, level, newSource, remainingNodes, Collections.emptyList());
		}

		private List<IPSTNode> getRemainingNodes(List<ChangeHandle> activeChanges) {			
			if (activeChanges.isEmpty()) {
				return nodes;
			}
			// Compute the remaining nodes by removing nodes that have been
			// successfully changed
			final Set<IPSTNode> removedNodes = Collections.newSetFromMap(new IdentityHashMap<>(activeChanges.size()));
			activeChanges.stream().map(c -> ((Change) c).getNode()).forEach(removedNodes::add);
			return nodes.stream().filter(n -> !removedNodes.contains(n)).collect(Collectors.toList());
		}

		private List<Change> getMergedPersistentChanges(List<ChangeHandle> activeChanges) {
			if (activeChanges.isEmpty()) {
				return persistentChanges;
			}
			final List<Change> merged = new ArrayList<>(persistentChanges.size() + activeChanges.size());
			getStreamOfAllChanges(activeChanges).forEachOrdered(merged::add);
			merged.sort(Comparator.comparingInt(c -> c.getNode().offset()));
			return merged;
		}

		private Stream<Change> getStreamOfAllChanges(List<ChangeHandle> activeChanges) {
			return Stream.concat(persistentChanges.stream(), activeChanges.stream().map(c -> (Change)c));
		}
		
		private List<IPSTNode> collectNodesOnLevel(IPSTTranslationUnit tu, int level) {
			final NodeCollector collector = new NodeCollector(level);
			tu.accept(collector);
			return collector.getResult();
		}
	}

	private final class NodeCollector implements IPSTVisitor {
		private final List<IPSTNode> result = new ArrayList<>();
		private final int targetLevel;
		int currentLevel;

		NodeCollector(int targetLevel) {
			this.targetLevel = targetLevel;
		}

		List<IPSTNode> getResult() {
			return result;
		}

		@Override
		public int defaultVisit(IPSTNode node) {
			if (strategy.skipSubTree(node)) {
				return PROCESS_SKIP;
			}
			if (currentLevel == targetLevel) {
				result.add(node);
				return PROCESS_SKIP;
			}
			++currentLevel;
			return PROCESS_CONTINUE;
		}

		@Override
		public int defaultLeave(IPSTNode node) {
			--currentLevel;
			return PROCESS_CONTINUE;
		}
	}
}
