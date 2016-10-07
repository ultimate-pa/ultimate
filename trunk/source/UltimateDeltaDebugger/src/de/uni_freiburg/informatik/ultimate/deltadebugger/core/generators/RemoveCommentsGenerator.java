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
	final ISourceDocument source;
	final List<MyChange> changes;
	
	private RemoveCommentsGenerator(ISourceDocument source, List<MyChange> changes) {
		this.source = source;
		this.changes = changes;
	}
	
	public static Optional<VariantGenerator> analyze(PassContext context) {
		final List<MyChange> changes = collectChanges(context.getSharedAST());
		return changes.isEmpty() ? Optional.empty()
				: Optional.of(new RemoveCommentsGenerator(context.getInput(), changes));
	}
	
	private static List<MyChange> collectChanges(IASTTranslationUnit ast) {
		final List<MyChange> changes = new ArrayList<>();
		for (IASTComment comment : ast.getComments()) {
			if (!comment.isPartOfTranslationUnitFile()) {
				continue;
			}
			IASTFileLocation loc = comment.getFileLocation();
			if (loc == null) {
				continue;
			}
			changes.add(new MyChange(changes.size(), loc.getNodeOffset(), loc.getNodeOffset() + loc.getNodeLength()));
		}
		return changes;
	}
	
	@Override
	public List<ChangeHandle> getChanges() {
		return Collections.unmodifiableList(changes);
	}
	
	@Override
	public String apply(List<ChangeHandle> activeChanges) {
		final SourceRewriter rewriter = new SourceRewriter(source);
		activeChanges.stream().forEach(c -> ((MyChange)c).apply(rewriter));
		return rewriter.apply();
	}
	
	private static class MyChange implements ChangeHandle {
		final int index;
		final int offset;
		final int endOffset;
		
		public MyChange(int index, int offset, int endOffset) {
			this.index = index;
			this.offset = offset;
			this.endOffset = endOffset;
		}

		void apply(SourceRewriter rewriter) {
			rewriter.replace(offset, endOffset, " ");
		}
		
		@Override
		public int getSequenceIndex() {
			return index;
		}
	}
}