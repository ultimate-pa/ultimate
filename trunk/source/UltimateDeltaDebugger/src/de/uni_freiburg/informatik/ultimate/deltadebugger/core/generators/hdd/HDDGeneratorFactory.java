package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGeneratorFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.ChangeGenerator.ExpansionResult;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes.Change;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

public class HDDGeneratorFactory implements IVariantGeneratorFactory {
	private final IHDDStrategy mStrategy;
	private final boolean mReparseBetweenLevels;

	public HDDGeneratorFactory() {
		this(new DefaultStrategy(), false);
	}

	public HDDGeneratorFactory(final IHDDStrategy strategy, final boolean reparseBetweenLevels) {
		mStrategy = strategy;
		mReparseBetweenLevels = reparseBetweenLevels;
	}

	@Override
	public Optional<IVariantGenerator> analyze(final IPassContext context) {
		return createGeneratorForFirstLevel(context);
	}

	public IHDDStrategy getStrategy() {
		return mStrategy;
	}

	public boolean isReparseBetweenLevelsEnabled() {
		return mReparseBetweenLevels;
	}

	public Optional<IVariantGenerator> createGeneratorForFirstLevel(final IPassContext context) {
		return createGeneratorForNextLevel(context, 0, context.getInput(), Arrays.asList(context.getSharedPst()),
				Collections.emptyList());
	}

	public Optional<IVariantGenerator> createGeneratorForNextLevel(final IPassContext context, final int currentLevel,
			final ISourceDocument source, final List<IPSTNode> nodes, final List<Change> persistentChanges) {
		final ChangeGenerator changeGenerator = new ChangeGenerator(context.getLogger(), mStrategy);
		final ExpansionResult expansion = changeGenerator.generateNextLevelChanges(nodes);
		if (expansion.mChangeGroups.isEmpty()) {
			return Optional.empty();
		}
		return Optional.of(new HDDGenerator(this, context, currentLevel + expansion.mAdvancedLevels, source,
				expansion.mRemainingNodes, expansion.mChangeGroups, persistentChanges));
	}
}
