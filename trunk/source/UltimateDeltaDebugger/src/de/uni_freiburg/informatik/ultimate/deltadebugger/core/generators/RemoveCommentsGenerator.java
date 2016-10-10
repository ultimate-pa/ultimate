package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTFileLocation;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.ChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.VariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public class RemoveCommentsGenerator implements VariantGenerator {
	private static class MyChange implements ChangeHandle {
		final int index;
		final int offset;
		final int endOffset;

		public MyChange(final int index, final int offset, final int endOffset) {
			this.index = index;
			this.offset = offset;
			this.endOffset = endOffset;
		}

		void apply(final SourceRewriter rewriter) {
			rewriter.replace(offset, endOffset, " ");
		}

		@Override
		public int getSequenceIndex() {
			return index;
		}
	}

	public static Optional<VariantGenerator> analyze(final PassContext context) {
		final List<MyChange> changes = collectChanges(context.getSharedAST());
		return changes.isEmpty() ? Optional.empty()
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

	final ISourceDocument source;

	final List<MyChange> changes;

	private RemoveCommentsGenerator(final ISourceDocument source, final List<MyChange> changes) {
		this.source = source;
		this.changes = changes;
	}

	@Override
	public String apply(final List<ChangeHandle> activeChanges) {
		final SourceRewriter rewriter = new SourceRewriter(source);
		activeChanges.stream().forEach(c -> ((MyChange) c).apply(rewriter));
		return rewriter.apply();
	}

	@Override
	public List<ChangeHandle> getChanges() {
		return Collections.unmodifiableList(changes);
	}
}