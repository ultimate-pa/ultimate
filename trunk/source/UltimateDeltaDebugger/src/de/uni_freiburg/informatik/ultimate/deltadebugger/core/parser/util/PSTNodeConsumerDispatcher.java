package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

public final class PSTNodeConsumerDispatcher {
	private final class DispatchVisitor implements IPSTVisitor {

		@Override
		public int defaultVisit(final IPSTNode node) {
			consumer.on(node);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTComment comment) {
			consumer.on(comment);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTConditionalBlock conditionalBlock) {
			consumer.on(conditionalBlock);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTDirective directive) {
			consumer.on(directive);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTIncludeDirective include) {
			consumer.on(include);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			consumer.on(literalRegion);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTMacroExpansion expansion) {
			consumer.on(expansion);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTRegularNode node) {
			consumer.on(node);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTTranslationUnit tu) {
			consumer.on(tu);
			return PROCESS_ABORT;
		}
	}

	private final IPSTNodeConsumer consumer;

	public PSTNodeConsumerDispatcher(final IPSTNodeConsumer consumer) {
		this.consumer = consumer;
	}

	public void dispatch(final IPSTNode node) {
		node.accept(new DispatchVisitor());
	}
}