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

import java.util.Map;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * A change of a PST node that can be applied by the HddGenerator.
 */
public abstract class HddChange implements IChangeHandle {
	private final IPSTNode mNode;
	private int mIndex = -1;
	
	/**
	 * @param node
	 *            PST node.
	 */
	public HddChange(final IPSTNode node) {
		mNode = node;
	}
	
	/**
	 * Applies a change.
	 * 
	 * @param rewriter
	 *            source rewriter
	 */
	public abstract void apply(SourceRewriter rewriter);
	
	public IPSTNode getNode() {
		return mNode;
	}
	
	@Override
	public int getSequenceIndex() {
		return mIndex;
	}
	
	/**
	 * @return {@code true} iff this change has a deferred change.
	 */
	public boolean hasDeferredChange() {
		return false;
	}
	
	public void setSequenceIndex(final int index) {
		mIndex = index;
	}
	
	/**
	 * Updates the deferred change.
	 * 
	 * @param deferredChangeMap
	 *            map (PST node -> deferred change)
	 */
	public void updateDeferredChange(final Map<IPSTNode, HddChange> deferredChangeMap) {
		throw new UnsupportedOperationException();
	}
	
	/**
	 * Creates an alternative change instance. Note that a new instance is required because the sequence index depends
	 * on the containing list.
	 * 
	 * @return an optional alternative to this change
	 */
	public Optional<HddChange> createAlternativeChange() {
		return Optional.empty();
	}
}
