/*
 * Copyright (C) 2018 Yannick Bühler (buehlery@tf.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.parser;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * @author Yannick Bühler
 * @since 2018-03-12
 */
public class IncludeSorter {

	/**
	 * The logger for emitting warnings about include cycles.
	 */
	private final ILogger mLogger;

	/**
	 * The symbol table to retrieve the include information from.
	 */
	private final MultiparseSymbolTable mSymTab;

	/**
	 * A map resolving normalized file names to translation units.
	 */
	private final Map<String, IASTTranslationUnit> mResolver;

	/**
	 * The units that already have been visited.
	 */
	private final Set<String> mVisited;

	/**
	 * The units that are currently in the subtree and have not been visited yet.
	 */
	private final Set<String> mOpen;

	/**
	 * The resulting sorted list.
	 */
	private final List<IASTTranslationUnit> mResult;

	public IncludeSorter(final ILogger logger, final Collection<IASTTranslationUnit> units,
			final MultiparseSymbolTable symTab) {
		mLogger = logger;
		mSymTab = symTab;
		mResolver = new HashMap<>();
		for (final IASTTranslationUnit unit : units) {
			mResolver.put(symTab.normalizeCDTFilename(unit.getFilePath()), unit);
		}
		mVisited = new HashSet<>();
		mOpen = new HashSet<>();
		mResult = new ArrayList<>();
		sort();
	}

	/**
	 * Sorts the translation units.
	 */
	private void sort() {
		for (final String unit : mResolver.keySet()) {
			if (mVisited.contains(unit)) {
				// Already part of another tree.
				continue;
			}
			assert mOpen.isEmpty();
			traverse(unit);
		}
	}

	/**
	 * Traverses translation units in post order and detects cycles.
	 * 
	 * @param unit
	 *            The unit, identified by its normalized file path.
	 */
	private void traverse(final String unit) {
		if (mOpen.contains(unit)) {
			mLogger.warn("Cycle detected: Second visit in path for " + unit);
			mLogger.warn("This might happen because include guards ('#ifndef #define...') or other mechanisms were not"
					+ " handled.");
			return;
		}
		mOpen.add(unit);
		for (final String include : mSymTab.getIncludesFor(unit)) {
			if (mVisited.contains(include)) {
				// This include has already been visited: All dependencies coming from it have been already processed.
				continue;
			}
			traverse(include);
		}
		mVisited.add(unit);
		mOpen.remove(unit);
		visit(unit);
	}

	/**
	 * Adds a translation unit to the result - all includes have been processed.
	 * 
	 * @param unit
	 *            The unit, identified by its normalized file path.
	 */
	private void visit(final String unit) {
		mResult.add(mResolver.get(unit));
	}

	public List<IASTTranslationUnit> getResult() {
		return mResult;
	}
}
