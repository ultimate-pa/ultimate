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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.changes;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HddChange;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Change by replacing a node with one of multiple alternatives.
 */
public class MultiReplaceChange extends HddChange {
	private final List<String> mReplacements;
	
	MultiReplaceChange(final IPSTNode node, final List<String> replacements) {
		super(node);
		if (replacements.isEmpty()) {
			throw new IllegalArgumentException("missing list of replacements");
		}
		mReplacements = replacements;
	}
	
	@Override
	public void apply(final SourceRewriter rewriter) {
		rewriter.replace(getNode(), mReplacements.get(0));
	}
	

	@Override
	public Optional<HddChange> createAlternativeChange() {
		if (mReplacements.size() > 1) {
			return Optional.of(new MultiReplaceChange(getNode(), mReplacements.subList(1, mReplacements.size())));
		}
		return Optional.empty();
	}

	
	@Override
	public String toString() {
		return "Replace " + getNode() + " (by one of ["
				+ mReplacements.stream().map(s -> "\"" + s + "\"").collect(Collectors.joining(", ")) + "])";
	}
}
