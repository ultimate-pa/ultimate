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

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGeneratorFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.ChangeGenerator.ExpansionResult;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;

/**
 * Factory for {@link HddGenerator}s.
 */
public class HddGeneratorFactory implements IVariantGeneratorFactory {
	private final IHddStrategy mStrategy;
	private final boolean mReparseBetweenLevels;
	
	/**
	 * Constructor with strategy.
	 * 
	 * @param strategy
	 *            strategy
	 * @param reparseBetweenLevels
	 *            {@code true} iff reparsing between levels should be used
	 */
	public HddGeneratorFactory(final IHddStrategy strategy, final boolean reparseBetweenLevels) {
		mStrategy = strategy;
		mReparseBetweenLevels = reparseBetweenLevels;
	}
	
	@Override
	public Optional<IVariantGenerator> analyze(final IPassContext context) {
		return createGeneratorForFirstLevel(context);
	}
	
	public IHddStrategy getStrategy() {
		return mStrategy;
	}
	
	public boolean isReparseBetweenLevelsEnabled() {
		return mReparseBetweenLevels;
	}
	
	/**
	 * @param context
	 *            Context.
	 * @return generator for the first level
	 */
	public Optional<IVariantGenerator> createGeneratorForFirstLevel(final IPassContext context) {
		return createGeneratorForNextLevel(context, 0, context.getInput(), Arrays.asList(context.getSharedPst()),
				Collections.emptyList());
	}
	
	/**
	 * @param context
	 *            Context.
	 * @param currentLevel
	 *            current level
	 * @param source
	 *            source
	 * @param nodes
	 *            PST nodes
	 * @param persistentChanges
	 *            persistent changes
	 * @return generator for the next level
	 */
	public Optional<IVariantGenerator> createGeneratorForNextLevel(final IPassContext context, final int currentLevel,
			final ISourceDocument source, final List<IPSTNode> nodes, final List<HddChange> persistentChanges) {
		final ChangeGenerator changeGenerator = new ChangeGenerator(context.getLogger(), mStrategy);
		final ExpansionResult expansion = changeGenerator.generateNextLevelChanges(nodes);
		if (expansion.mChangeGroups.isEmpty()) {
			return Optional.empty();
		}
		return Optional.of(new HddGenerator(this, context, currentLevel + expansion.mAdvancedLevels, source,
				expansion.mRemainingNodes, expansion.mChangeGroups, persistentChanges));
	}
}
