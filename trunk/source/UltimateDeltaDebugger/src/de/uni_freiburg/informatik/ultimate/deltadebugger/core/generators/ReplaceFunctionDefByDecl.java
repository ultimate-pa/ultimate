package de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.ChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassContext;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.VariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.SourceRewriter;

public class ReplaceFunctionDefByDecl implements VariantGenerator {
	final ISourceDocument source;
	final List<MyChange> changes;

	private ReplaceFunctionDefByDecl(ISourceDocument source, List<MyChange> changes) {
		this.source = source;
		this.changes = changes;
	}

	public static Optional<VariantGenerator> analyze(PassContext context) {
		final List<MyChange> changes = collectChanges(context.getSharedPST());
		return changes.isEmpty() ? Optional.empty()
				: Optional.of(new ReplaceFunctionDefByDecl(context.getInput(), changes));
	}

	private static List<MyChange> collectChanges(IPSTTranslationUnit tu) {
		final List<MyChange> changes = new ArrayList<>();
		tu.accept(new IPSTVisitor() {
			@Override
			public int visit(IPSTRegularNode node) {
				IASTNode astNode = node.getASTNode();
				if (astNode instanceof IASTFunctionDefinition) {
					IPSTRegularNode body = node.findRegularChild(((IASTFunctionDefinition) astNode).getBody());
					if (body != null) {
						changes.add(new MyChange(changes.size(), body));
					}
					return PROCESS_SKIP;
				}

				return PROCESS_CONTINUE;
			}
		});

		return changes;
	}

	@Override
	public List<ChangeHandle> getChanges() {
		return Collections.unmodifiableList(changes);
	}

	@Override
	public String apply(List<ChangeHandle> activeChanges) {
		final SourceRewriter rewriter = new SourceRewriter(source);
		activeChanges.stream().forEach(c -> ((MyChange) c).apply(rewriter));
		return rewriter.apply();
	}

	private static class MyChange implements ChangeHandle {
		final int index;
		final IPSTRegularNode node;

		public MyChange(int index, IPSTRegularNode node) {
			this.index = index;
			this.node = node;
		}

		void apply(SourceRewriter rewriter) {
			rewriter.replace(node, ";");
		}

		@Override
		public int getSequenceIndex() {
			return index;
		}
	}
}