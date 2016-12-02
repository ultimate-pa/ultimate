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
import org.eclipse.cdt.internal.formatter.scanner.Scanner;
import org.eclipse.cdt.internal.formatter.scanner.Token;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IPassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

/**
 * Removes Tokens.
 */
public final class RemoveTokens implements IVariantGenerator {
	private final ISourceDocument mSource;
	private final List<TokenChange> mChanges;

	private RemoveTokens(final ISourceDocument source, final List<TokenChange> changes) {
		mSource = source;
		mChanges = changes;
	}

	@Override
	public String apply(final List<IChangeHandle> activeChanges) {
		final SourceRewriter rewriter = new SourceRewriter(mSource);
		activeChanges.stream().forEach(c -> ((TokenChange) c).apply(rewriter));
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
		final List<TokenChange> changes = getTokenChanges(context.getInput());
		return changes.isEmpty() ? Optional.empty() : Optional.of(new RemoveTokens(context.getInput(), changes));
	}

	private static List<TokenChange> getTokenChanges(final ISourceDocument source) {
		Scanner scanner = new Scanner();
		scanner.setSource(source.getText().toCharArray());

		final List<TokenChange> changes = new ArrayList<>();
		Token token = scanner.nextToken();
		while (token != null) {
			if (!token.isWhiteSpace()) {
				changes.add(new TokenChange(changes.size(), token.getOffset(), token.getLength()));
			}
			token = scanner.nextToken();
		}

		return changes;
	}

	/**
	 * A change handle.
	 */
	private static class TokenChange implements IChangeHandle {
		private final int mIndex;
		private final int mOffset;
		private final int mLength;

		public TokenChange(final int index, final int offset, final int length) {
			mIndex = index;
			mOffset = offset;
			mLength = length;
		}

		void apply(final SourceRewriter rewriter) {
			rewriter.replace(mOffset, mOffset + mLength, " ");
		}

		@Override
		public int getSequenceIndex() {
			return mIndex;
		}
	}
}
