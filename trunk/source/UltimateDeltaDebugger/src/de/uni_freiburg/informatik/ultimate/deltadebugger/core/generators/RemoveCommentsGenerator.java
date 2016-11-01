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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Removes comments.
 */
public final class RemoveCommentsGenerator implements IVariantGenerator {
	private final ISourceDocument mSource;
	private final List<MyChange> mChanges;
	
	private RemoveCommentsGenerator(final ISourceDocument source, final List<MyChange> changes) {
		mSource = source;
		mChanges = changes;
	}
	
	@Override
	public String apply(final List<IChangeHandle> activeChanges) {
		final SourceRewriter rewriter = new SourceRewriter(mSource);
		activeChanges.stream().forEach(c -> ((MyChange) c).apply(rewriter));
		return rewriter.apply();
	}
	
	@Override
	public List<IChangeHandle> getChanges() {
		return Collections.unmodifiableList(mChanges);
	}
	
	/**
	 * @param context
	 *            Pass context.
	 * @return result
	 */
	public static Optional<IVariantGenerator> analyze(final IPassContext context) {
		final List<MyChange> changes = collectChanges(context.getSharedAst());
		return changes.isEmpty()
				? Optional.empty()
				: Optional.of(new RemoveCommentsGenerator(context.getInput(), changes));
	}
	
	private static List<MyChange> collectChanges(final IASTTranslationUnit ast) {
		final List<MyChange> changes = new ArrayList<>();
		for (final IASTComment comment : ast.getComments()) {
			if (!comment.isPartOfTranslationUnitFile()) {
				continue;
			}
			final IASTFileLocation loc = comment.getFileLocation();
			if (loc == null) {
				continue;
			}
			changes.add(new MyChange(changes.size(), loc.getNodeOffset(), loc.getNodeOffset() + loc.getNodeLength()));
		}
		return changes;
	}
	
	/**
	 * Change handler.
	 */
	private static class MyChange implements IChangeHandle {
		private final int mIndex;
		private final int mOffset;
		private final int mEndOffset;
		
		public MyChange(final int index, final int offset, final int endOffset) {
			mIndex = index;
			mOffset = offset;
			mEndOffset = endOffset;
		}
		
		void apply(final SourceRewriter rewriter) {
			rewriter.replace(mOffset, mEndOffset, " ");
		}
		
		@Override
		public int getSequenceIndex() {
			return mIndex;
		}
	}
}
